
val fetch_byte : unit -> bits(8)

enum operand_type = {LargeConst, SmallConst, FetchVariable, Omitted}

struct branch = {
  direction : bool,
  offset : bits(14),
}

function perform_branch(branch : branch, cond : bool) -> unit = {
  let cond = if branch.direction then cond else not_bool(cond);
  if cond then {
    if branch.offset == 0b00000000000000 then routine_return(0x0000)
    else if branch.offset == 0b00000000000001 then routine_return(0x0001)
    else PC = PC + sail_sign_extend(branch.offset, 20) - 0x00002
  }
}

function decode_variable(operand : bits(16)) -> bits(8) = {
  if operand >_u 0x00ff then throw InvalidVariableOperand(operand) else truncate(operand, 8)
}

function desc_op(x : operand) -> string = {
  match x {
    Constant(bs) => hex_str(unsigned(bs)),
    Variable(vr) => "v" @ hex_str(unsigned(vr)),
  }
}

function desc_op_list(xs : list(operand)) -> string = {
  var l = xs;
  var s = "[";
  while (is_cons(l)) do {
    let (h,t) = head_tail(l);
    l = t;
    s = s @ desc_op(h);
    if is_cons(t) then s = s @ ", ";
  };
  s = s @ "]";
  s
}

function desc_branch(b : branch) -> string = {
  if b.direction then hex_str(signed(b.offset)) else "!" @ hex_str(signed(b.offset))
}

function desc_r(r : bits(8)) -> string = " -> " @ hex_str(unsigned(r))

function resolve_operand_list(l : list(operand)) -> list(bits(16)) = {
  var l_in = l;
  var l_out : list(bits(16)) = [| |];
  while (is_cons(l_in)) do {
    let (h,t) = head_tail(l_in);
    let h' = resolve_operand(h);
    l_in = t;
    l_out = h'::l_out;
  };
  reverse(l_out)
}

// Some opcodes are followed by more data than the generic operands
val fetch_result_destination : unit -> bits(8)
val fetch_string : unit -> list(zscii)
val fetch_branch : unit -> branch

scattered union instr ('operand : Type)

val decode_0op : bits(4) -> instr(operand)
val decode_1op : (bits(4), operand) -> instr(operand)
val decode_2op : (bits(5), operand, operand) -> instr(operand)
val decode_var : (bits(5), list(operand)) -> instr(operand)
val decode_je : (list(operand)) -> instr(operand)
val decode_ext : (bits(8), list(operand)) -> instr(operand)

val describe : instr(operand) -> string
val resolve_instr : instr(operand) -> instr(bits(16))
val execute : instr(bits(16)) -> unit

scattered function decode_0op
scattered function decode_1op
scattered function decode_2op
scattered function decode_var
scattered function decode_ext
scattered function describe
scattered function resolve_instr
scattered function execute

union clause instr = JE : ('operand, list('operand), branch)
function clause decode_2op (0b00001, a, b) = JE(a, [| b |], fetch_branch())
function clause describe JE(a, bs, branch) = "je " @ desc_op(a) @ " " @ desc_op_list(bs) @ " " @ desc_branch(branch)
function clause resolve_instr JE(a, bs, branch) = JE(resolve_operand(a), resolve_operand_list(bs), branch)
function decode_je(operands) = match operands {
  [| |] => throw MalformedInstruction("je with no operands"),
  [| _ |] => throw MalformedInstruction("je with 1 operand"),
  h :: t => JE (h, t, fetch_branch())
}
// TODO: is this the right semantics for >2 operands?
function clause execute JE(a, bs, branch) = {
  var bs' = bs;
  var cond : bool = false;
  while is_cons(bs') do {
    let (h,t) = head_tail(bs');
    cond = cond | a == h;
    bs' = t;
  };
  perform_branch(branch, cond)
}

union clause instr = JL : ('operand, 'operand, branch)
function clause decode_2op (0b00010, a, b) = JL(a, b, fetch_branch())
function clause describe JL(a, b, branch) = "jl " @ desc_op(a) @ " " @ desc_op(b) @ " " @ desc_branch(branch)
function clause resolve_instr JL(a, b, branch) = JL(resolve_operand(a), resolve_operand(b), branch)
function clause execute JL(a, b, branch) = perform_branch(branch, a <_s b)

union clause instr = JG : ('operand, 'operand, branch)
function clause decode_2op (0b00011, a, b) = JG(a, b, fetch_branch())
function clause describe JG(a, b, branch) = "jg " @ desc_op(a) @ " " @ desc_op(b) @ " " @ desc_branch(branch)
function clause resolve_instr JG(a, b, branch) = JG(resolve_operand(a), resolve_operand(b), branch)
function clause execute JG(a, b, branch) = perform_branch(branch, a >_s b)

union clause instr = DecChk : ('operand, 'operand, branch)
function clause decode_2op (0b00100, variable, value) = DecChk(variable, value, fetch_branch())
function clause describe DecChk(a, b, branch) = "dec_chk " @ desc_op(a) @ " " @ desc_op(b) @ " " @ desc_branch(branch)
function clause resolve_instr DecChk(variable, value, branch) = DecChk(resolve_operand(variable), resolve_operand(value), branch)
function clause execute DecChk(variable, value, branch) = {
  let variable = decode_variable(variable);
  // Assuming signed because dec is signed
  // The spec says this happens "in place", but that's meaningless because the stack ends up the same length
  let v = read_variable(variable) - 0x0001;
  write_variable(variable, v);
  perform_branch(branch, v <_s value);
}

union clause instr = IncChk : ('operand, 'operand, branch)
function clause decode_2op (0b00101, variable, value) = IncChk(variable, value, fetch_branch())
function clause describe IncChk(a, b, branch) = "inc_chk " @ desc_op(a) @ " " @ desc_op(b) @ " " @ desc_branch(branch)
function clause resolve_instr IncChk(variable, value, branch) = IncChk(resolve_operand(variable), resolve_operand(value), branch)
function clause execute IncChk(variable, value, branch) = {
  let variable = decode_variable(variable);
  // Assuming signed because dec is signed
  let v = read_variable(variable) + 0x0001;
  write_variable(variable, v);
  perform_branch(branch, v >_s value);
}

union clause instr = JIn : ('operand, 'operand, branch)
function clause decode_2op (0b00110, obj1, obj2) = JIn(obj1, obj2, fetch_branch())
function clause describe JIn(a, b, branch) = "jin " @ desc_op(a) @ " " @ desc_op(b) @ " " @ desc_branch(branch)
function clause resolve_instr JIn(obj1, obj2, branch) = JIn(resolve_operand(obj1), resolve_operand(obj2), branch)
function clause execute JIn(obj1, obj2, branch) = perform_branch(branch, object_parent(obj1) == obj2)

union clause instr = Test : ('operand, 'operand, branch)
function clause decode_2op (0b00111, bitmap, flags) = Test(bitmap, flags, fetch_branch())
function clause describe Test(a, b, branch) = "test " @ desc_op(a) @ " " @ desc_op(b) @ " " @ desc_branch(branch)
function clause resolve_instr Test(obj1, obj2, branch) = Test(resolve_operand(obj1), resolve_operand(obj2), branch)
function clause execute Test(bitmap, flags, branch) = perform_branch(branch, (bitmap & flags) == flags)

union clause instr = Or : ('operand, 'operand, bits(8))
function clause decode_2op (0b01000, x, y) = Or(x,y,fetch_result_destination())
function clause describe Or(a, b, r) = "or " @ desc_op(a) @ " " @ desc_op(b) @ desc_r(r)
function clause resolve_instr Or(x, y, r) = Or(resolve_operand(x), resolve_operand(y), r)
function clause execute Or(x, y, r) = write_variable(r, x | y)

union clause instr = And : ('operand, 'operand, bits(8))
function clause decode_2op (0b01001, x, y) = And(x,y,fetch_result_destination())
function clause describe And(a, b, r) = "and " @ desc_op(a) @ " " @ desc_op(b) @ desc_r(r)
function clause resolve_instr And(x, y, r) = And(resolve_operand(x), resolve_operand(y), r)
function clause execute And(x, y, r) = write_variable(r, x & y)

union clause instr = TestAttr : ('operand, 'operand, branch)
function clause decode_2op (0b01010, object, attribute) = TestAttr(object, attribute, fetch_branch())
function clause describe TestAttr(a, b, branch) = "test_attr " @ desc_op(a) @ " " @ desc_op(b) @ " " @ desc_branch(branch)
function clause resolve_instr TestAttr(obj, attr, branch) = TestAttr(resolve_operand(obj), resolve_operand(attr), branch)
function clause execute TestAttr(object, attribute, branch) = {
  let cond = test_attribute(object, attribute);
  perform_branch(branch, cond)
}

union clause instr = SetAttr : ('operand, 'operand)
function clause decode_2op (0b01011, object, attribute) = SetAttr(object, attribute)
function clause describe SetAttr(a, b) = "set_attr " @ desc_op(a) @ " " @ desc_op(b)
function clause resolve_instr SetAttr(obj, attr) = SetAttr(resolve_operand(obj), resolve_operand(attr))
function clause execute SetAttr(object, attribute) = set_attribute(object, attribute)

union clause instr = ClearAttr : ('operand, 'operand)
function clause decode_2op (0b01100, object, attribute) = ClearAttr(object, attribute)
function clause describe ClearAttr(a, b) = "clear_attr " @ desc_op(a) @ " " @ desc_op(b)
function clause resolve_instr ClearAttr(obj, attr) = ClearAttr(resolve_operand(obj), resolve_operand(attr))
function clause execute ClearAttr(object, attribute) = clear_attribute(object, attribute)

union clause instr = InsertObj : ('operand, 'operand)
function clause decode_2op (0b01110, object, destination) = InsertObj(object, destination)
function clause describe InsertObj(a, b) = "insert_obj " @ desc_op(a) @ " " @ desc_op(b)
function clause resolve_instr InsertObj(obj, dest) = InsertObj(resolve_operand(obj), resolve_operand(dest))
function clause execute InsertObj(object, destination) = {
  // TODO: Should we remove object beforehand?
  set_object_parent(object, destination);
  set_object_sibling(object, object_child(destination));
  set_object_child(destination, object);
}

union clause instr = LoadW : ('operand, 'operand, bits(8))
function clause decode_2op (0b01111, x, y) = LoadW(x,y,fetch_result_destination())
function clause describe LoadW(a, b, r) = "loadw " @ desc_op(a) @ " " @ desc_op(b) @ desc_r(r)
function clause resolve_instr LoadW(x, y, r) = LoadW(resolve_operand(x), resolve_operand(y), r)
function clause execute LoadW(array, index, destination) = {
  // The spec doesn't explicitly say so, but praxix expects that the index is signed
  let addr = sail_zero_extend(array, 20) + sail_sign_extend(index, 20) << 1;
  if addr >_u 0x0fffe then throw LoadAddressOverflow(addr);
  write_variable(destination, read_word(addr))
}

union clause instr = LoadB : ('operand, 'operand, bits(8))
function clause decode_2op (0b10000, x, y) = LoadB(x,y,fetch_result_destination())
function clause describe LoadB(a, b, r) = "loadb " @ desc_op(a) @ " " @ desc_op(b) @ desc_r(r)
function clause resolve_instr LoadB(x, y, r) = LoadB(resolve_operand(x), resolve_operand(y), r)
function clause execute LoadB(array, index, destination) = {
  // The spec doesn't explicitly say so, but praxix expects that the index is signed
  let addr = sail_zero_extend(array, 20) + sail_sign_extend(index, 20);
  if addr >_u 0x0ffff then throw LoadAddressOverflow(addr);
  write_variable(destination, sail_zero_extend(read_byte(addr), 16))
}

union clause instr = GetProp : ('operand, 'operand, bits(8))
function clause decode_2op (0b10001, x, y) = GetProp(x, y, fetch_result_destination())
function clause describe GetProp(a, b, r) = "get_prop " @ desc_op(a) @ " " @ desc_op(b) @ desc_r(r)
function clause resolve_instr GetProp(x, y, r) = GetProp(resolve_operand(x), resolve_operand(y), r)
function clause execute GetProp(object, property, r) = {
  let value = get_property(object, property);
  write_variable(r, value)
}

union clause instr = GetPropAddr : ('operand, 'operand, bits(8))
function clause decode_2op (0b10010, x, y) = GetPropAddr(x, y, fetch_result_destination())
function clause describe GetPropAddr(a, b, r) = "get_prop_addr " @ desc_op(a) @ " " @ desc_op(b) @ desc_r(r)
function clause resolve_instr GetPropAddr(x, y, r) = GetPropAddr(resolve_operand(x), resolve_operand(y), r)
function clause execute GetPropAddr(object, property, r) = {
  match get_property_address(object, property, false) {
    Some((addr, _)) => write_variable(r, truncate(addr, 16)), // TODO: overflow
    None() => write_variable(r, 0x0000),
  }
}

union clause instr = GetNextProp : ('operand, 'operand, bits(8))
function clause decode_2op (0b10011, obj, prop) = GetNextProp(obj, prop, fetch_result_destination())
function clause describe GetNextProp(a, b, r) = "get_next_prop " @ desc_op(a) @ " " @ desc_op(b) @ desc_r(r)
function clause resolve_instr GetNextProp(x, y, r) = GetNextProp(resolve_operand(x), resolve_operand(y), r)
function clause execute GetNextProp(object, property, r) = write_variable(r, get_next_property(object, property))

union clause instr = Add : ('operand, 'operand, bits(8))
function clause decode_2op (0b10100, x, y) = Add(x,y,fetch_result_destination())
function clause describe Add(a, b, r) = "add " @ desc_op(a) @ " " @ desc_op(b) @ desc_r(r)
function clause resolve_instr Add(x, y, r) = Add(resolve_operand(x), resolve_operand(y), r)
function clause execute Add(x, y, r) = write_variable(r, x + y)

union clause instr = Sub : ('operand, 'operand, bits(8))
function clause decode_2op (0b10101, x, y) = Sub(x,y,fetch_result_destination())
function clause describe Sub(a, b, r) = "sub " @ desc_op(a) @ " " @ desc_op(b) @ desc_r(r)
function clause resolve_instr Sub(x, y, r) = Sub(resolve_operand(x), resolve_operand(y), r)
function clause execute Sub(x, y, r) = write_variable(r, x - y)

union clause instr = Mul : ('operand, 'operand, bits(8))
function clause decode_2op (0b10110, x, y) = Mul(x,y,fetch_result_destination())
function clause describe Mul(a, b, r) = "mul " @ desc_op(a) @ " " @ desc_op(b) @ desc_r(r)
function clause resolve_instr Mul(x, y, r) = Mul(resolve_operand(x), resolve_operand(y), r)
function clause execute Mul(x, y, r) = write_variable(r, add_bits_int(sail_zeros(16), signed(x) * signed(y)))

union clause instr = Div : ('operand, 'operand, bits(8))
function clause decode_2op (0b10111, x, y) = Div(x,y,fetch_result_destination())
function clause describe Div(a, b, r) = "div " @ desc_op(a) @ " " @ desc_op(b) @ desc_r(r)
function clause resolve_instr Div(x, y, r) = Div(resolve_operand(x), resolve_operand(y), r)
function clause execute Div(x, y, r) = {
  if y == 0x0000 then throw DivisionByZero();
  // TODO: check which division
  write_variable(r, add_bits_int(sail_zeros(16), tdiv_int(signed(x), signed(y))))
}

union clause instr = Mod : ('operand, 'operand, bits(8))
function clause decode_2op (0b11000, x, y) = Mod(x,y,fetch_result_destination())
function clause describe Mod(a, b, r) = "mod " @ desc_op(a) @ " " @ desc_op(b) @ desc_r(r)
function clause resolve_instr Mod(x, y, r) = Mod(resolve_operand(x), resolve_operand(y), r)
function clause execute Mod(x, y, r) = {
  if y == 0x0000 then throw DivisionByZero();
  // TODO: check which division
  write_variable(r, add_bits_int(sail_zeros(16), tmod_int(signed(x), signed(y))))
}

union clause instr = Call2s : ('operand, 'operand, bits(8))
function clause decode_2op ((0b11001, routine, arg) if version >= 4) = Call2s(routine, arg, fetch_result_destination())
function clause describe Call2s(a, b, r) = "call2s " @ desc_op(a) @ " " @ desc_op(b) @ desc_r(r)
function clause resolve_instr Call2s(x, y, r) = Call2s(resolve_operand(x), resolve_operand(y), r)
function clause execute Call2s(routine, arg, r) = routine_call(unpack_address(routine, PackCall), [| arg |], Some(r))

union clause instr = Call2n : ('operand, 'operand)
function clause decode_2op ((0b11010, routine, arg) if version >= 5) = Call2n(routine, arg)
function clause describe Call2n(a, b) = "call2n " @ desc_op(a) @ " " @ desc_op(b)
function clause resolve_instr Call2n(x, y) = Call2n(resolve_operand(x), resolve_operand(y))
function clause execute Call2n(routine, arg) = routine_call(unpack_address(routine, PackCall), [| arg |], None())

union clause instr = Store : ('operand, 'operand)
function clause decode_2op (0b01101, variable, value) = Store(variable, value)
function clause describe Store(a, b) = "store " @ desc_op(a) @ " " @ desc_op(b)
function clause resolve_instr Store(x, y) = Store(resolve_operand(x), resolve_operand(y))
function clause execute Store(vr, vl) = write_variable_no_push(decode_variable(vr), vl)

union clause instr = JZ : ('operand, branch)
function clause decode_1op (0x0, x) = JZ(x, fetch_branch())
function clause describe JZ(x, branch) = "jz " @ desc_op(x) @ " " @ desc_branch(branch)
function clause resolve_instr JZ(x, branch) = JZ(resolve_operand(x), branch)
function clause execute JZ(operand, branch) = perform_branch(branch, operand == 0x0000)

union clause instr = GetSibling : ('operand, bits(8), branch)
function clause decode_1op (0x1, object) = {
  let r = fetch_result_destination();
  let b = fetch_branch();
  GetSibling(object, r, b)
}
function clause describe GetSibling(x, r, branch) = "get_sibling " @ desc_op(x) @ desc_r(r) @ " " @ desc_branch(branch)
function clause resolve_instr GetSibling(x, r, branch) = GetSibling(resolve_operand(x), r, branch)
function clause execute GetSibling(object, r, branch) = {
  let sibling = object_sibling(object);
  write_variable(r, sibling);
  perform_branch(branch, sibling != 0x0000)
}

union clause instr = GetChild : ('operand, bits(8), branch)
function clause decode_1op (0x2, object) = {
  let r = fetch_result_destination();
  let b = fetch_branch();
  GetChild(object, r, b)
}
function clause describe GetChild(x, r, branch) = "get_child " @ desc_op(x) @ desc_r(r) @ " " @ desc_branch(branch)
function clause resolve_instr GetChild(x, r, branch) = GetChild(resolve_operand(x), r, branch)
function clause execute GetChild(object, r, branch) = {
  let child = object_child(object);
  write_variable(r, child);
  perform_branch(branch, child != 0x0000)
}

union clause instr = GetParent : ('operand, bits(8))
function clause decode_1op (0x3, object) = GetParent(object, fetch_result_destination())
function clause describe GetParent(x, r) = "get_parent " @ desc_op(x) @ desc_r(r)
function clause resolve_instr GetParent(x, r) = GetParent(resolve_operand(x), r)
function clause execute GetParent(object, r) = {
  let parent = object_parent(object);
  write_variable(r, parent);
}

union clause instr = GetPropLen : ('operand, bits(8))
function clause decode_1op (0x4, x) = GetPropLen(x, fetch_result_destination())
function clause describe GetPropLen(x, r) = "get_prop_len " @ desc_op(x) @ desc_r(r)
function clause resolve_instr GetPropLen(x, r) = GetPropLen(resolve_operand(x), r)
function clause execute GetPropLen(prop, r) = write_variable(r, get_property_length(sail_zero_extend(prop, 20)))

union clause instr = Inc : 'operand
function clause decode_1op (0x5, v) = Inc(v)
function clause describe Inc(x) = "inc " @ desc_op(x)
function clause resolve_instr Inc(v) = Inc(resolve_operand(v))
function clause execute Inc(variable) = {
  let variable = decode_variable(variable);
  let value = read_variable(variable);
  write_variable(variable, value + 0x0001)
}

union clause instr = Dec : 'operand
function clause decode_1op (0x6, v) = Dec(v)
function clause describe Dec(x) = "dec " @ desc_op(x)
function clause resolve_instr Dec(v) = Dec(resolve_operand(v))
function clause execute Dec(variable) = {
  let variable = decode_variable(variable);
  let value = read_variable(variable);
  write_variable(variable, value - 0x0001)
}

union clause instr = PrintAddr : 'operand
function clause decode_1op (0x7, x) = PrintAddr(x)
function clause describe PrintAddr(x) = "print_addr " @ desc_op(x)
function clause resolve_instr PrintAddr(x) = PrintAddr(resolve_operand(x))
function clause execute PrintAddr(addr) = {
  let (_, s) = read_z_coded_string(sail_zero_extend(addr, 20));
  print_zscii_string(s)
}

union clause instr = Call1s : ('operand, bits(8))
function clause decode_1op ((0x8, routine) if version >= 4) = Call1s(routine, fetch_result_destination())
function clause decode_1op (0x8, _) = throw MalformedInstruction("call_1s on version < 4")
function clause describe Call1s(x, r) = "call1s " @ desc_op(x) @ desc_r(r)
function clause resolve_instr Call1s(x, r) = Call1s(resolve_operand(x), r)
function clause execute Call1s(routine, r) = routine_call(unpack_address(routine, PackCall), [| |], Some(r))

union clause instr = RemoveObj : 'operand
function clause decode_1op (0x9, obj) = RemoveObj(obj)
function clause describe RemoveObj(x) = "remove_obj " @ desc_op(x)
function clause resolve_instr RemoveObj(obj) = RemoveObj(resolve_operand(obj))
function clause execute RemoveObj(object) = {
  let parent = object_parent(object);
  var sibling = object_child(parent);
  if sibling == object then set_object_child(parent, object_sibling(object)) else {
    while sibling != 0x0000 & object_sibling(sibling) != object do sibling = object_sibling(sibling);
    if sibling != 0x0000 then set_object_sibling(sibling, object_sibling(object));
  };
  set_object_sibling(object, 0x0000);
  set_object_parent(object, 0x0000)
}

union clause instr = PrintObj : 'operand
function clause decode_1op (0xa, x) = PrintObj(x)
function clause describe PrintObj(x) = "print_obj " @ desc_op(x)
function clause resolve_instr PrintObj(x) = PrintObj(resolve_operand(x))
function clause execute PrintObj(object) = {
  let base_addr = object_properties(object);
  let (_, s) = read_z_coded_string(base_addr + 0x00001);
  print_zscii_string(s)
}

union clause instr = Ret : 'operand
function clause decode_1op (0xb, x) = Ret(x)
function clause describe Ret(x) = "ret " @ desc_op(x)
function clause resolve_instr Ret(x) = Ret(resolve_operand(x))
function clause execute Ret(value) = routine_return(value)

union clause instr = Jump : 'operand
function clause decode_1op (0xc, offset) = Jump(offset)
function clause describe Jump(x) = "jump " @ desc_op(x)
function clause resolve_instr Jump(x) = Jump(resolve_operand(x))
function clause execute Jump(offset) = PC = PC + sail_sign_extend(offset, 20) - 0x00002

union clause instr = PrintPaddr : 'operand
function clause decode_1op (0xd, x) = PrintPaddr(x)
function clause describe PrintPaddr(x) = "print_paddr " @ desc_op(x)
function clause resolve_instr PrintPaddr(x) = PrintPaddr(resolve_operand(x))
function clause execute PrintPaddr(paddr) = {
  let (_, s) = read_z_coded_string(unpack_address(paddr, PackPrint));
  print_zscii_string(s)
}

union clause instr = Load : ('operand, bits(8))
function clause decode_1op (0xe, v) = Load(v, fetch_result_destination())
function clause describe Load(x, r) = "load " @ desc_op(x) @ desc_r(r)
function clause resolve_instr Load(v, r) = Load(resolve_operand(v), r)
function clause execute Load(v, r) = write_variable(r, read_variable_no_pop(decode_variable(v)))

union clause instr = Not : ('operand, bits(8))
function clause decode_1op ((0xf, v) if version <= 4) = Not(v, fetch_result_destination())
function clause describe Not(x, r) = "not " @ desc_op(x) @ desc_r(r)
function clause resolve_instr Not(v, r) = Not(resolve_operand(v), r)
function clause execute Not(v, r) = write_variable(r, not_vec(v))

union clause instr = Call1n : 'operand
function clause decode_1op (0xf, v) = Call1n(v)
function clause describe Call1n(x) = "call1n " @ desc_op(x)
function clause resolve_instr Call1n(x) = Call1n(resolve_operand(x))
function clause execute Call1n(routine) = routine_call(unpack_address(routine, PackCall), [| |], None())

union clause instr = RTrue : unit
function clause decode_0op 0x0 = RTrue()
function clause describe RTrue() = "rtrue"
function clause resolve_instr RTrue() = RTrue()
function clause execute RTrue() = routine_return(0x0001)

union clause instr = RFalse : unit
function clause decode_0op 0x1 = RFalse()
function clause describe RFalse() = "rfalse"
function clause resolve_instr RFalse() = RFalse()
function clause execute RFalse() = routine_return(0x0000)

union clause instr = Print : list(zscii)
function clause decode_0op 0x2 = Print(fetch_string())
function clause describe Print(s) = "print " @ zscii_to_string(s)
function clause resolve_instr Print(x) = Print(x)
function clause execute Print(s) = print_zscii_string(s)

union clause instr = PrintRet : list(zscii)
function clause decode_0op 0x3 = PrintRet(fetch_string())
function clause describe PrintRet(s) = "print_ret " @ zscii_to_string(s)
function clause resolve_instr PrintRet(x) = PrintRet(x)
function clause execute PrintRet(s) = {
  print_zscii_string(s);
  print_endline("");
  routine_return(0x0001);
}

union clause instr = Nop : unit
function clause decode_0op 0x4 = Nop()
function clause describe Nop() = "nop"
function clause resolve_instr Nop() = Nop()
function clause execute Nop() = ()

union clause instr = RetPopped : unit
function clause decode_0op 0x8 = RetPopped()
function clause describe RetPopped() = "ret_popped"
function clause resolve_instr RetPopped() = RetPopped()
function clause execute RetPopped() = routine_return(pop())

union clause instr = Quit : unit
function clause decode_0op 0xa = Quit()
function clause describe Quit() = "quit"
function clause resolve_instr Quit() = Quit()
function clause execute Quit() = quit = true

union clause instr = NewLine : unit
function clause decode_0op 0xb = NewLine()
function clause describe NewLine() = "new_line"
function clause resolve_instr NewLine() = NewLine()
function clause execute NewLine() = print_endline("")

union clause instr = Verify : branch
function clause decode_0op (0xd if version >= 3) = Verify(fetch_branch())
function clause decode_0op 0xd = throw MalformedInstruction("verify on version < 3")
function clause describe Verify(branch) = "verify " @ desc_branch(branch)
function clause resolve_instr Verify(b) = Verify(b)
function clause execute Verify(branch) = {
  let length = file_length();
  prerr_int("length ", length);
  // TODO: this fails the czech test, not sure why
  var checksum : bits(16) = 0x0000;
  foreach (i from 64 to (length - 1)) {
    checksum = checksum + sail_zero_extend(read_byte(add_bits_int(0x00000, i)), 16)
  };
  perform_branch(branch, checksum == read_word(0x0001c));
}

union clause instr = Piracy : branch
function clause decode_0op (0xf if version >= 5) = Piracy(fetch_branch())
function clause decode_0op 0xf = throw MalformedInstruction("piracy on version < 3")
function clause describe Piracy(branch) = "piracy " @ desc_branch(branch)
function clause resolve_instr Piracy(b) = Piracy(b)
function clause execute Piracy(branch) = perform_branch(branch, genuine_flag)


union clause instr = PutProp : ('operand, 'operand, 'operand)
function clause decode_var (0b00011, [| object, property, value |]) = PutProp(object, property, value)
function clause decode_var (0b00011, _) = throw MalformedInstruction("put_prop with invalid operand(s)")
function clause describe PutProp(a, b, c) = "put_prop " @ desc_op(a) @ " " @ desc_op(b) @ " " @ desc_op(c)
function clause resolve_instr PutProp(obj, prop, v) = PutProp(resolve_operand(obj), resolve_operand(prop), resolve_operand(v))
function clause execute PutProp(object, property, value) = set_property(object, property, value)

union clause instr = PrintChar : 'operand
function clause decode_var (0b00101, operands) =
  match operands {
    [| code |] => PrintChar(code),
    _ => throw MalformedInstruction("print_char with invalid operand(s)"),
  }
function clause describe PrintChar(x) = "print_char " @ desc_op(x)
function clause resolve_instr PrintChar(c) = PrintChar(resolve_operand(c))
function clause execute PrintChar(char) = if char <_u 0x0400 then print_zscii(truncate(char, 10)) else throw BadCharacter(char)

union clause instr = PrintNum : 'operand
function clause decode_var (0b00110, operands) =
  match operands {
    [| n |] => PrintNum(n),
    _ => throw MalformedInstruction("print_num with invalid operand(s)"),
  }
function clause describe PrintNum(x) = "print_num " @ desc_op(x)
function clause resolve_instr PrintNum(x) = PrintNum(resolve_operand(x))
function clause execute PrintNum(n) = print(dec_str(signed(n)))

union clause instr = CallVs2 : ('operand, list('operand), bits(8))
function clause decode_var ((0b01100, routine::args) if version >= 4) = CallVs2(routine, args, fetch_result_destination())
function clause decode_var ((0b01100, [| |]) if version >= 4) = throw MalformedInstruction("call_vs2 without routine")
function clause decode_var  (0b01100, _) = throw MalformedInstruction("call_vs2 on version < 4")
function clause describe CallVs2(a, bs, r) = "callvs2 " @ desc_op(a) @ " " @ desc_op_list(bs) @ desc_r(r)
function clause resolve_instr CallVs2(x, xs, r) = CallVs2(resolve_operand(x), resolve_operand_list(xs), r)
function clause execute CallVs2(routine, args, r) = routine_call(unpack_address(routine, PackCall), args, Some(r))

union clause instr = Call : ('operand, list('operand), bits(8))
function clause decode_var (0b00000, operands) =
  match operands {
    [| |] => throw MalformedInstruction("call without routine"),
    routine::arguments => Call(routine, arguments, fetch_result_destination()),
  }
function clause describe Call(a, bs, r) = "call " @ desc_op(a) @ " " @ desc_op_list(bs) @ desc_r(r)
function clause resolve_instr Call(x, xs, r) = Call(resolve_operand(x), resolve_operand_list(xs), r)
function clause execute Call(routine, arguments, destination) = {
  let routine = unpack_address(routine, PackCall);
  if routine == 0x00000 then write_variable(destination, 0x0000) else routine_call(routine, arguments, Some(destination))
}

union clause instr = StoreW : ('operand, 'operand, 'operand)
function clause decode_var (0b00001, operands) = match operands {
  [| array, index, value |] => StoreW(array, index, value),
  _ => throw MalformedInstruction("storeb without 3 operands")
}
function clause describe StoreW(a, b, c) = "storew " @ desc_op(a) @ " " @ desc_op(b) @ " " @ desc_op(c)
function clause resolve_instr StoreW(x, y, z) = StoreW(resolve_operand(x), resolve_operand(y), resolve_operand(z))
function clause execute StoreW(array, index, value) = {
  // The spec doesn't explicitly say so, but praxix expects that the index is signed
  let addr = sail_zero_extend(array, 20) + sail_sign_extend(index, 20) << 1;
  if addr >_u 0x0fffe then throw LoadAddressOverflow(addr);
  write_word(addr, value)
}

union clause instr = StoreB : ('operand, 'operand, 'operand)
function clause decode_var (0b00010, operands) = match operands {
  [| array, index, value |] => StoreB(array, index, value),
  _ => throw MalformedInstruction("storeb without 3 operands")
}
function clause describe StoreB(a, b, c) = "storeb " @ desc_op(a) @ " " @ desc_op(b) @ " " @ desc_op(c)
function clause resolve_instr StoreB(x, y, z) = StoreB(resolve_operand(x), resolve_operand(y), resolve_operand(z))
function clause execute StoreB(array, index, value) = {
  // The spec doesn't explicitly say so, but praxix expects that the index is signed
  let addr = sail_zero_extend(array, 20) + sail_sign_extend(index, 20);
  if addr >_u 0x0ffff then throw LoadAddressOverflow(addr);
  if value >_u 0x00ff then warn("Oversize byte store"); // Not sure if this is allowed
  write_byte(addr, truncate(value, 8))
}

union clause instr = Random : ('operand, bits(8))
function clause decode_var (0b00111, [| range |]) = Random(range, fetch_result_destination())
function clause decode_var (0b00111, _) = throw MalformedInstruction("random with wrong operands")
function clause describe Random(x, r) = "random " @ desc_op(x) @ desc_r(r)
function clause resolve_instr Random(x, r) = Random(resolve_operand(x), r)
function clause execute Random(range, r) = {
  let range = signed(range);
  if range > 0 then write_variable(r, add_bits_int(0x0000, random_range(1, range))) else
  if range == 0 then { prerr("Warning range called with zero"); write_variable(r, 0x0000) } else {
    random_seed(0 - range);
    write_variable(r, 0x0000);
  }
}

union clause instr = Push : 'operand
function clause decode_var (0b01000, [| value |]) = Push(value)
function clause decode_var (0b01000, _) = throw MalformedInstruction("push with wrong operands")
function clause describe Push(x) = "push " @ desc_op(x)
function clause resolve_instr Push(x) = Push(resolve_operand(x))
function clause execute Push(value) = push(value)

union clause instr = Pull : 'operand
function clause decode_var (0b01001, [| variable |]) = Pull(variable)
function clause describe Pull(x) = "pull " @ desc_op(x)
function clause resolve_instr Pull(r) = Pull(resolve_operand(r))
// TODO: version 6 behaviour
function clause execute Pull(variable) = write_variable_no_push(decode_variable(variable), pop())

union clause instr = SetTextStyle : 'operand
function clause decode_var ((0b10001, [| style |]) if version >= 4) = SetTextStyle(style)
function clause decode_var  (0b10001, _) = throw MalformedInstruction("set_text_style on version < 4")
function clause describe SetTextStyle(x) = "set_text_style " @ desc_op(x)
function clause resolve_instr SetTextStyle(x) = SetTextStyle(resolve_operand(x))
function clause execute SetTextStyle(style) = {
  // TODO
  prerr_bits("unimplemented set_text_style ", style);
}

union clause instr = Not5 : ('operand, bits(8))
function clause decode_var ((0b11000, [| vl |]) if version >= 5) = Not5(vl, fetch_result_destination())
function clause decode_var ((0b11000, _) if version >= 5) = throw MalformedInstruction("Not with wrong operands")
function clause decode_var  (0b11000, _) = throw MalformedInstruction("Not on version < 5")
function clause describe Not5(x, r) = "not5 " @ desc_op(x) @ desc_r(r)
function clause resolve_instr Not5(x, r) = Not5(resolve_operand(x), r)
function clause execute Not5(value, r) = write_variable(r, not_vec(value))

union clause instr = CallVn : ('operand, list('operand))
function clause decode_var ((0b11001, routine::args) if version >= 5) = CallVn(routine, args)
function clause decode_var ((0b11001, _) if version >=5) = throw MalformedInstruction("call_vn without routine")
function clause decode_var (0b11001, _) = throw MalformedInstruction("call_vn on version < 5")
function clause describe CallVn(a, bs) = "callvn " @ desc_op(a) @ " " @ desc_op_list(bs)
function clause resolve_instr CallVn(x, xs) = CallVn(resolve_operand(x), resolve_operand_list(xs))
function clause execute CallVn(routine, args) = routine_call(unpack_address(routine, PackCall), args, None())

union clause instr = CallVn2 : ('operand, list('operand))
function clause decode_var ((0b11010, routine::args) if version >= 5) = CallVn2(routine, args)
function clause decode_var ((0b11010, [| |]) if version >= 5) = throw MalformedInstruction("call_vn2 without routine")
function clause decode_var  (0b11010, _) = throw MalformedInstruction("call_vn2 on version < 5")
function clause describe CallVn2(a, bs) = "callvn2 " @ desc_op(a) @ " " @ desc_op_list(bs)
function clause resolve_instr CallVn2(x, xs) = CallVn2(resolve_operand(x), resolve_operand_list(xs))
function clause execute CallVn2(routine, args) = routine_call(unpack_address(routine, PackCall), args, None())

union clause instr = CheckArgCount : ('operand, branch)
function clause decode_var ((0b11111, [| number |]) if version >= 5) = CheckArgCount(number, fetch_branch())
function clause decode_var ((0b11111, _) if version >= 5) = throw MalformedInstruction("check_arg_count with wrong operands")
function clause decode_var (0b11111, _) = throw MalformedInstruction("check_arg_count on version < 5")
function clause describe CheckArgCount(x, branch) = "check_arg_count " @ desc_op(x) @ " " @ desc_branch(branch)
function clause resolve_instr CheckArgCount(x, branch) = CheckArgCount(resolve_operand(x), branch)
function clause execute CheckArgCount(number, branch) = perform_branch(branch, unsigned(number) <= number_arguments)

union clause instr = Read : ('operand, 'operand, option(('operand, 'operand)), option(bits(8)))
// The spec doesn't say that there's a two operand form in v5, but it's used in the praxix test
function clause decode_var (0b00100, [| text, parse |]) = Read(text, parse, None(), if version >= 5 then Some(fetch_result_destination()) else None())
function clause decode_var ((0b00100, [| text, parse, time, routine |]) if version >= 4) =
  Read(text, parse, Some((time, routine)), if version >= 5 then Some(fetch_result_destination()) else None())
function clause decode_var (0b00100, _) = throw MalformedInstruction("read with wrong number of operands")
function clause describe Read(x, y, z, r) = "read " @ desc_op(x) @ " " @ desc_op(y) @ " " @ (match z { Some((a, b)) => desc_op(a) @ " " @ desc_op(b) @ " ", None() => ""}) @ (match r { Some(r') => desc_r(r'), None() => "" })
function clause resolve_instr Read(x, y, z, r) = Read(resolve_operand(x), resolve_operand(y), match z { Some((a, b)) => Some((resolve_operand(a), resolve_operand(b))), None() => None() }, r)

val byte_is_in : forall 'n. (implicit('n), vector('n, dec, bits(8)), bits(8)) -> bool

function byte_is_in(size, chars, char) = {
  var found : bool = false;
  foreach (i from 0 to (size - 1)) {
    if chars[i] == char then found = true;
  };
  found
}

struct dictionary_info = {
  entry_length : nat,
  number_entries : nat,
  entries_start : address,
}

function read_dictionary_info(dictionary : address, number_word_separators : nat) -> dictionary_info = {
  let info : dictionary_info = struct {
    entry_length = unsigned(read_byte(add_bits_int(dictionary, number_word_separators + 1))),
    number_entries = unsigned(read_word(add_bits_int(dictionary, number_word_separators + 2))),
    entries_start = add_bits_int(dictionary, number_word_separators + 4),
  };
  if info.entry_length < (if version <= 3 then 4 else 6) then throw InvalidDictionaryEntryLength(info.entry_length);
  info
}

val lookup_entry : forall 'n. (implicit('n), dictionary_info, vector('n, bits(8))) -> address

function lookup_entry(size_zchars, dictionary, zchars) = {
  // We ought to be able to do a binary search here, but keep it simple
  foreach (i from 1 to dictionary.number_entries) {
    let entry = add_bits_int(dictionary.entries_start, i * dictionary.entry_length);
    var found : bool = true;
    foreach (j from 0 to (size_zchars - 1)) {
      found = found & read_byte(add_bits_int(entry, j)) == zchars[j]
    };
    if found then return entry;
  };
  0x00000
}

function clause execute Read(text, parse, timer, r) = {
  // TODO: status line
  let text_addr = sail_zero_extend(text, 20);
  let existing_characters = if version >= 5 then unsigned(read_byte(text_addr + 0x00001)) else 0;
  let max_characters = unsigned(read_byte(text_addr)) - existing_characters;
  // TODO: max < 0?
  var s : string = match timer {
    None() => read_command_plain(max_characters),
    Some(_) => unimplemented("timer callback"),
  };
  // Write the string into memory
  let new_start_addr = add_bits_int(text_addr, if version < 5 then 1 else existing_characters + 2);
  var i : int = 0;
  var more : bool = true;
  while i < max_characters & more do {
    match string_destruct(s) {
      None() => more = false,
      Some(c,t) => {
        // TODO: terminating characters table
        if c == 10 then more = false else {
          s = t;
	  write_byte(add_bits_int(new_start_addr, i), add_bits_int(0x00, c));
	  i = i + 1;
        }
      }
    }
  };
  let total_characters = existing_characters + i;
  if more then unreachable("read overflow!");
  if version < 5 then {
    write_byte(add_bits_int(new_start_addr, total_characters), 0x00);
  } else {
    write_byte(text_addr + 0x00001, add_bits_int(0x00, total_characters));
  };
  // Perform lexical analysis
  if parse != 0x0000 | version < 5 then {
    let parse_addr = sail_zero_extend(parse, 20);
    let max_words = unsigned(read_byte(parse_addr));
    let dictionary = sail_zero_extend(read_word(0x00008), 20);
    let 'number_word_separators = unsigned(read_byte(dictionary));
    var word_separators : vector('number_word_separators + 1, bits(8)) = vector_init(0x32);
    if number_word_separators >= 1 then {
      foreach (i from 1 to number_word_separators) {
        word_separators[i] = read_byte(add_bits_int(dictionary, i))
      }
    };
    let dictionary_info = read_dictionary_info(dictionary, number_word_separators);

    var j : int = 0;
    var words : int = 0;
    let start_addr = add_bits_int(text_addr, if version < 5 then 1 else 2);
    let 'encode_triplets = if version <= 3 then 2 else 3;
    let empty_entry : vector('encode_triplets * 3, bits(5)) = vector_init(0b00101);

    while words < max_words & j < total_characters do {
      var char = read_byte(add_bits_int(start_addr, j));
      if char == 0x20 then j = j + 1
      else if byte_is_in(word_separators, char) then {
        let (encoded, _) = encode_zscii(empty_entry, 0, char);
        let word_entry = add_bits_int(parse_addr, 2 + 4 * words);
        let dictionary_entry = lookup_entry(dictionary_info, pack_zchars(encoded));
        // TODO: if dictionary_entry >_u 0x0ffff then
        write_word(word_entry, truncate(dictionary_entry, 16));
	write_byte(word_entry + 0x00002, 0x01);
	write_byte(word_entry + 0x00003, add_bits_int(0x00, j));
	words = words + 1;
	j = j + 1;
      } else {
        var k : int = 0;
        var encoded_i : nat = 0;
        var encoded = empty_entry;
        while j + k < total_characters & char != 0x20 & not_bool(byte_is_in(word_separators, char)) do {
          (encoded, encoded_i) = encode_zscii(encoded, encoded_i, char);
          k = k + 1;
          if j + k < total_characters then char = read_byte(add_bits_int(start_addr, j + k));
        };
        let word_entry = add_bits_int(parse_addr, 2 + 4 * words);
        let dictionary_entry = lookup_entry(dictionary_info, pack_zchars(encoded));
        // TODO: if dictionary_entry >_u 0x0ffff then
        write_word(word_entry, truncate(dictionary_entry, 16));
	write_byte(word_entry + 0x00002, add_bits_int(0x00, k));
	write_byte(word_entry + 0x00003, add_bits_int(0x00, j));
	words = words + 1;
        j = j + k;
      }
    };
    write_byte(parse_addr + 0x00001, add_bits_int(0x00, words));
  };
  // i.e., version >= 5
  // TODO: use the actual terminating character
  match r {
    None() => (),
    Some(r') => write_variable(r', 0x000d),
  }
}

union clause instr = LogShift : ('operand, 'operand, bits(8))
function clause decode_ext (0x02, [| value, places |]) = LogShift(value, places, fetch_result_destination())
function clause decode_ext (0x02, _) = throw MalformedInstruction("log_shift with bad operands")
function clause describe LogShift(a, b, r) = "log_shift " @ desc_op(a) @ " " @ desc_op(b) @ desc_r(r)
function clause resolve_instr LogShift(x, y, r) = LogShift(resolve_operand(x), resolve_operand(y), r)
function clause execute LogShift(value, places, r) = {
  let shift = signed(places);
  if shift < -15 | shift > 15 then {
    warn("out over range shift " @ dec_str(shift) @ " at ");
    write_variable(r, 0x0000)
  } else {
    let result = if shift >= 0 then value << shift else value >> (0 - shift);
    write_variable(r, result)
  }
}

union clause instr = ArtShift : ('operand, 'operand, bits(8))
function clause decode_ext (0x03, [| value, places |]) = ArtShift(value, places, fetch_result_destination())
function clause decode_ext (0x03, _) = throw MalformedInstruction("art_shift with bad operands")
function clause describe ArtShift(a, b, r) = "art_shift " @ desc_op(a) @ " " @ desc_op(b) @ desc_r(r)
function clause resolve_instr ArtShift(x, y, r) = ArtShift(resolve_operand(x), resolve_operand(y), r)
function clause execute ArtShift(value, places, r) = {
  let shift = signed(places);
  if shift < -15 | shift > 15 then {
    warn("out over range shift " @ dec_str(shift) @ " at ");
    write_variable(r, if shift < -15 then replicate_bits(value[15..15], 16) else 0x0000)
  } else {
    let result = if shift >= 0 then value << shift else value >>> (0 - shift);
    write_variable(r, result)
  }
}

union clause instr = SaveUndo : bits(8)
function clause decode_ext ((0x09, [| |]) if version >= 5) = SaveUndo(fetch_result_destination())
function clause decode_ext ((0x09, _) if version >= 5) = throw MalformedInstruction("save_undo with operands")
function clause decode_ext  (0x09, _) = throw MalformedInstruction("save_undo when version < 5")
function clause describe SaveUndo(r) = "save_undo" @ desc_r(r)
function clause resolve_instr SaveUndo(r) = SaveUndo(r)
function clause execute SaveUndo(r) = {
  // TODO: undo
  write_variable(r, 0xffff)
}

function clause decode_0op op = unimplemented("Unmodelled 0op instruction " @ bits_str(op))
function clause decode_1op (op,_) = unimplemented("Unmodelled 1op instruction " @ bits_str(op))
function clause decode_2op (op,_,_) = unimplemented("Unmodelled 2op instruction " @ bits_str(op))
function clause decode_var (op,_) = unimplemented("Unmodelled var instruction " @ bits_str(op))
function clause decode_ext (op,_) = unimplemented("Unmodelled ext instruction " @ bits_str(op))

end decode_0op
end decode_1op
end decode_2op
end decode_var
end decode_ext
end instr
end describe
end resolve_instr
end execute
