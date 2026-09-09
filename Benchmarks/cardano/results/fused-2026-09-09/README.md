# Fused CEK result archive

See the [measurement report](../../../../docs/reviews/cardano-fused-preparation-2026-09-09.md)
for methodology, interpretation, and reproduction instructions. Each preparation
has a separate `-proof.json` measured immediately afterwards. JSON records keep
their original source, revision, patch, and runner hashes; only absolute log
paths are shortened to basenames. Full logs remain in the local experiment
workspace and can be regenerated with the harness.

| Files | Meaning |
|---|---|
| `final-sellnft-1800-*`, `final-governance-9000-*` | Final complete named evaluator, three alternating pairs per workload. |
| `paired-global-*` | Complete indexed evaluator, three alternating pairs; implementation unchanged by the later named extension. |
| `final-summary.json` | Median/min/max of the preceding three workloads. Total wall time is calculated per prep/proof pair before summarizing. |
| `complete-secondary-*` | Final complete named evaluator, one pair each for MintingPolicy and ParamFeed. |
| `fused-global1800.json` | Higher-bound timeout at 240 seconds; excluded from completed-run summaries. |
| `paired-sellnft-*`, `summary.json` | Historical initial SellNFT series with the partial named adapter; the old summary also includes the unchanged global series. |
| `secondary-*` | Historical single pairs using the partial named adapter, including the Governance fallback regression that motivated completing constructor/case fusion. |

SellNFT proof rows intentionally retain `status: error`: its existing
multisatisfaction timeout is present in every pair, alongside two Valid results
and two expected counterexamples. It is included in total time, not counted as
a passed query. No early WSC scout with an unwired interpreter option contributes
to these summaries.
