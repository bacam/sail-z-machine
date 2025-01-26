function routine_call(routine : address, arguments : list(bits(16)), destination : option(bits(8))) -> unit = {
  //prerr_bits("routine ", routine);
  let number_locals = unsigned(read_byte(routine));
  let locals_from_arguments : list(bits(16)) = list_take(arguments, number_locals);
  var new_locals : list(bits(16)) = [| |];
  foreach (i from number_locals downto (length(locals_from_arguments) + 1)) {
    let v = if version < 5 then read_word(add_bits_int(routine, 2*i)) else 0x0000;
    new_locals = v::new_locals;
  };
  new_locals = locals_from_arguments @ new_locals;
  routine_stack = (locals, stack, number_arguments, destination, PC)::routine_stack;
  locals = new_locals;
  stack = [| |];
  number_arguments = length(arguments);
  PC = add_bits_int(routine, if version < 5 then 2*number_locals+1 else 1);
  //prerr_bits("new pc ", PC)
}

function routine_return(v : bits(16)) -> unit = {
//prerr_endline("return");
  match routine_stack {
    [| |] => unimplemented("end of stack"),
    (locals', stack', number_arguments', destination, caller_pc)::t => {
      locals = locals';
      stack = stack';
      number_arguments = number_arguments';
      routine_stack = t;
      PC = caller_pc;
      match destination {
        None() => (),
        Some(variable) => write_variable(variable, v),
      }
    }
  }
}
