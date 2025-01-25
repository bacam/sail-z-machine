function routine_return(v : bits(16)) -> unit = {
//prerr_endline("return");
  match routine_stack {
    [| |] => unimplemented("end of stack"),
    (locals', stack', destination, caller_pc)::t => {
      locals = locals';
      stack = stack';
      routine_stack = t;
      PC = caller_pc;
      match destination {
        None() => (),
        Some(variable) => write_variable(variable, v),
      }
    }
  }
}
