# Shared static backend selection for generated ranked Goblint adapters.
# The including script must define [extraction_directory].

rank_worklist_name=${RANK_WORKLIST:-bitmap}

case "$rank_worklist_name" in
  bitmap)
    rank_worklist_source="$extraction_directory/rank_worklist_bitmap.ml"
    ;;
  binary)
    rank_worklist_source="$extraction_directory/rank_worklist_binary_heap.ml"
    ;;
  pqueue)
    rank_worklist_source="$extraction_directory/rank_worklist_pqueue.ml"
    ;;
  *)
    echo "unknown RANK_WORKLIST backend: $rank_worklist_name" >&2
    echo "expected one of: bitmap, binary, pqueue" >&2
    exit 1
    ;;
esac

if [ ! -f "$rank_worklist_source" ]; then
  echo "missing rank worklist backend: $rank_worklist_source" >&2
  exit 1
fi
