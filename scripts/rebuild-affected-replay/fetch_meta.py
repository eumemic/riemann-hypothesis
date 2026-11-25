"""Download the public CI records of the batch commits: each commit's receipt and module manifest.

usage: fetch_meta.py OUT_DIR

A module manifest lists, for every module of the tree, the Lake input hash it was compiled with and
the bundle (`.ltar`) that holds its outputs."""
import json, os, sys, urllib.request

BASE = "https://rh-cache.taucetiproject.org/"
# main before batch b2, then after each of the batches b2 ... b20
COMMITS = ["a28ad7ec8b9f5ff4ec448fe210d3ac57aacfffe1", "343b1de38bbe4c5c66f1c1c0afd7c34e8645acdf",
           "c9883164b0b3d762cee21f889d03d59a53b3ba3b", "bb9476b875a219608a9068f8f18d8c56b4e7f1ca",
           "1cd97d8aa4a16681b109389ab18eefa4b2ba36d8", "1da818b50f1e18808db2792b9dc735bda8cb84d8",
           "307cef33f046955ee79dba47e0d828d06496d75f", "9282d3a102c4aff0e6026746db2a8990f5d9cddd",
           "67c00ce1025a73f81a39533ac42deb47f15c4a15", "4a5b4a2d2a5177a2b6cb876425f0cb4cb6b85061",
           "c40250a50104b7e02e7d74f658d00fa7b1f4827c", "fcb6eac7534875d32d68030967e2deae6d686151",
           "27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59", "a18a350c3e5aad997766cff2670b292313e46574",
           "246656fc62ac80c1214f48550138076c4f278569", "ef451fc356cbc66861df031531aaafd2843797ac",
           "251c7b05dd869ceba1aa42c6001c00b4010f23f9", "8e5cefeeaffe7e4c12153385b7bb33fb7223c41a",
           "d91ae2678eea19a0c3045ffca37f1da757c2e719", "91b273530883b723ef4422436e0dc3557749325a"]


def get(url):
    request = urllib.request.Request(url, headers={"User-Agent": "curl/8"})
    with urllib.request.urlopen(request, timeout=300) as response: return response.read()


if __name__ == "__main__":
    out = sys.argv[1]
    os.makedirs(out, exist_ok=True)
    for sha in COMMITS:
        receipt = get(f"{BASE}ci/revisions/{sha}.json")
        with open(os.path.join(out, f"rev-{sha[:10]}.json"), "wb") as f: f.write(receipt)
        record = json.loads(receipt)
        manifest = os.path.join(out, f"mm-{record['module_manifest_sha256'][:12]}.jsonl.gz")
        if not os.path.exists(manifest):
            with open(manifest, "wb") as f: f.write(get(BASE + record["module_manifest_key"]))
        print(sha[:10], os.path.basename(manifest), flush=True)
