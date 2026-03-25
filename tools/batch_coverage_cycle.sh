#!/bin/bash
# 批量执行: 对每个 filter 运行 solver -> coverage_audit -> 保存报告
# 输出写入 /tmp/ 避免终端崩溃

set -e
cd "$(dirname "$0")/.."
CACHE="disasm_cache_sm100a.merged.txt"
LOG_DIR="/tmp/nv_isa_batch"
REPORT_DIR="docs/coverage_reports"
mkdir -p "$LOG_DIR" "$REPORT_DIR"

FILTERS="${1:-F2FP UTCCP I2FP UTCHMMA UTCSIFT PRMT DADD ATOMG DFMA FADD IMAD}"

for f in $FILTERS; do
  echo "[$(date +%H:%M:%S)] === $f solver ==="
  python3 -m nv_isa_solver.instruction_solver \
    --arch SM100a --cache_file "$CACHE" --num_parallel 10 --filter "$f" \
    > "$LOG_DIR/${f}_solver.log" 2>&1 || true

  echo "[$(date +%H:%M:%S)] === $f coverage_audit ==="
  python3 tools/coverage_audit.py \
    --cache_file "$CACHE" --isa_json isa.json --output_dir output \
    --report_md "$REPORT_DIR/coverage_${f}.md" \
    > "$LOG_DIR/${f}_coverage.log" 2>&1 || true

  echo "[$(date +%H:%M:%S)] $f done"
done

echo "Done. Logs: $LOG_DIR"
echo "Reports: $REPORT_DIR"
