- C++17
- **Boost** (header-only: `boost::multiprecision` — პაკეტი: `libboost-all-dev` ან `libboost-dev`)
- **nlohmann/json** (header-only: `libnlohmann-json-dev`)
- **libsecp256k1** (პაკეტი: `libsecp256k1-dev`)
- **OpenSSL** SHA256-თვის (`libssl-dev`)

## ინსტალაცია Debian/Ubuntu-ზე:
```bash
sudo apt-get update
sudo apt-get install -y g++ libboost-dev libsecp256k1-dev libssl-dev nlohmann-json3-dev
```

## კომპილაცია:
```bash
g++ -O3 -std=c++17 recover_stronger.cpp -o recover_stronger -lsecp256k1 -lcrypto -lpthread
```

## RUN/გაშვება:
```bash
./recover_stronger \
  --sigs signatures.jsonl \
  --export-clusters dupR_clusters.jsonl \
  --report-collisions r_collisions.jsonl \
  --preload-k recovered_k.jsonl \
  --max-iter 12 \
  --threads 8 \
  --scan-random-k 250 \
  --scan-random-k-top 0 \
  --scan-random-k-range 4294967296 \
  --verify-pass -v
```
## შენიშვნა:
- **ეს კოდი არ ითვლის z-ს (სიგჰეშს); ელოდება, რომ z უკვე უწერია თითო ჩანაწერს**

###
```txt
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
```
