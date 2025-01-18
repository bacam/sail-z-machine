function warn(msg : string) -> unit = prerr_bits("Warning: " @ msg, PC)

function main() -> unit = {
  init();
  try {
    while true do {
      //prerr_bits("PC: ", PC);
      let instr = fetch_and_decode();
      execute(instr)
    }
  } catch {
    Unimplemented(s) => prerr_endline("Unimplemented: " @ s),
    StackUnderflow() => prerr_bits("Stack unflow at ", PC),
    NoSuchLocal(i) => prerr_bits("No such local " @ dec_str(i) @ " at ", PC),
    NestedAbbreviation() => prerr_endline("Nested abbreviation"),
  }
}
