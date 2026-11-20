default Order dec
$include <prelude.sail>

type segment_fields = { 'n, 'n > 0 & 'n <= 8. int('n) }

mapping segment_encoding : bits(3) <-> segment_fields = {
  0b000 <-> 1, 0b001 <-> 2, 0b010 <-> 3, 0b011 <-> 4,
  0b100 <-> 5, 0b101 <-> 6, 0b110 <-> 7, 0b111 <-> 8,
}

union instruction = { Segment : segment_fields }

mapping encoding : instruction <-> bits(3) = { Segment(n) <-> segment_encoding(n) }
