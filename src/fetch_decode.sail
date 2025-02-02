
function to_type(t : bits(2)) -> operand_type =
  match t {
  0b00 => LargeConst,
  0b01 => SmallConst,
  0b10 => FetchVariable,
  0b11 => Omitted,
  }

function fetch_byte() = {
  let addr = PC;
  let byte = read_byte(addr);
  // TODO: overflow?
  PC = addr + 0x00001;
  byte
}

function fetch_long_operand(ty : bits(1)) -> operand =
  match ty {
  0b0 => Constant(sail_zero_extend(fetch_byte(), 16)),
  0b1 => Variable(fetch_byte())
  }

function fetch_result_destination() = fetch_byte()

function fetch_string() = {
  let (new_pc, string) = read_z_coded_string(PC);
  PC = new_pc;
  string
}

function fetch_operand(ty : operand_type) -> operand = {
  match ty {
    Omitted => unreachable("Omitted operand type where operand expected"),
    SmallConst => Constant(sail_zero_extend(fetch_byte(), 16)),
    LargeConst => Constant(fetch_byte() @ fetch_byte()),
    FetchVariable => Variable(fetch_byte()),
  }
}

function resolve_operand(v : operand) -> bits(16) = {
  match v {
    Constant(vl) => vl,
    Variable(vr) => read_variable(vr),
  }
}

function fetch_var_operand_types() -> list(operand_type) = {
  let types_byte = fetch_byte();
  match to_type(types_byte[7..6]) {
    Omitted => { if types_byte[5..0] != 0b111111 then warn("malformed arguments"); [| |] },
    ty1 => {
      match to_type(types_byte[5..4]) {
        Omitted => { if types_byte[3..0] != 0b1111 then warn("malformed arguments"); [| ty1 |] },
        ty2 => {
          match to_type(types_byte[3..2]) {
            Omitted => { if types_byte[1..0] != 0b11 then warn("malformed arguments"); [| ty1, ty2 |] },
            ty3 => {
              match to_type(types_byte[1..0]) {
                Omitted => [| ty1, ty2, ty3 |],
                ty4 => [| ty1, ty2, ty3, ty4 |],
	      }
	    }
          }
        }
      }
    }
  }
}

function fetch_branch() -> branch = {
  let b1 = fetch_byte();
  let direction = b1[7] == bitone;
  let offset : bits(14) =
    match b1[6] {
      bitone => sail_zero_extend(b1[5..0], 14),
      bitzero => {
        let b2 = fetch_byte();
	b1[5..0] @ b2
      }
    };
  struct { direction, offset }
}

function fetch_and_decode() -> instr(operand) = {
  let opcode1 = fetch_byte();
  match opcode1 {
    0xbe if version >= 5 => {
      let op = fetch_byte();
      var operand_types = fetch_var_operand_types();
      var operands : list(operand) = [| |];
      while is_cons(operand_types) do {
        let (ty,tys) = head_tail(operand_types);
	operands = fetch_operand(ty)::operands;
	operand_types = tys;
      };
      operands = reverse(operands);
      decode_ext(op, operands)
    },
    0b11 @ var_operands @ (op : bits(5)) => {
      var operand_types = fetch_var_operand_types();
      // call_vs2 and call_vn2 can take up to 8 operands
      if var_operands == 0b1 & (op == 0b01100 | op == 0b11010) then {
        let types2 = fetch_var_operand_types();
	if length(operand_types) < 4 & is_cons(types2) then {
	  throw MalformedInstruction("Bad second operand types byte")
	} else {
	  operand_types = operand_types @ types2
	}
      };
      var operands : list(operand) = [| |];
      while is_cons(operand_types) do {
        let (ty,tys) = head_tail(operand_types);
	operands = fetch_operand(ty)::operands;
	operand_types = tys;
      };
      operands = reverse(operands);
      match var_operands {
        0b0 => match operands {
	  [| operand1, operand2 |] => decode_2op(op, operand1, operand2),
	  // Section 15 says je takes variable operands, even though 4.5 says 2OPs take 2
	  _ if op == 0b00001 => decode_je(operands),
	  _ => throw MalformedInstruction("2op didn't have exactly two operands"),
	},
	0b1 => decode_var(op, operands),
      }
    },
    0b10 @ (ty : bits(2)) @ op => { // short form
      match to_type(ty) {
        Omitted => decode_0op(op),
	ty' => {
          let operand = fetch_operand(to_type(ty));
          decode_1op(op, operand)
	}
      }
    },
    0b0 @ (ty1 : bits(1)) @ (ty2 : bits(1)) @ op => { // long form
      let operand1 = fetch_long_operand(ty1);
      let operand2 = fetch_long_operand(ty2);
      decode_2op(op, operand1, operand2)
    }
  }
}
