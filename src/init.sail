function init () -> unit = {
  let start = read_word(0x00006);
  if version >= 6 then {
    unimplemented("call")
  } else {
    PC = sail_zero_extend(start, 20)
  }
}
