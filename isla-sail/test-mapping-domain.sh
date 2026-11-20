#!/bin/sh
set -eu
ir=$(mktemp -d)
trap 'rm -rf "$ir"' EXIT
env -u DUNE_DIR_LOCATIONS sail -plugin "$PWD/$1" -isla --isla-preserve encoding_forwards \
  --isla-preserve segment_encoding_backwards --isla-output-dir "$ir" -o mapping-domain "$2"
awk '
  /^fn zsegment_encoding_backwards(_infallible)?\(/ { bodies++; in_mapping=1; next }
  in_mapping && /^}/ { in_mapping=0 }
  in_mapping && /zisla_type_assume.*@gt\(zargz3, 0\)/ { lower++ }
  in_mapping && /zisla_type_assume.*@lteq\(zargz3, 8\)/ { upper++ }
  END {
    if (bodies != 2 || lower != bodies || upper != bodies) {
      print "expected both bounds in both mapping variants, found", bodies, lower, upper
      exit 1
    }
  }
' "$ir/mapping-domain.ir"
