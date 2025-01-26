function init () -> unit = {
  let start = read_word(0x00006);
  let flags2 = read_word(0x00010);
  // TODO: undo support
  if version >= 5 then write_word(0x00010, flags2 & 0b1111111111101111);
  if version >= 6 then {
    unimplemented("call")
  } else {
    PC = sail_zero_extend(start, 20)
  }
}
