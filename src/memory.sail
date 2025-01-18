// Rather implicit in the spec, but they're normally written as 5 hex digits
// and the largest packed address appears to be 4*<16 bits> + 8*<16 bits>
type address = bits(20)

register PC : address

val read_byte : address -> bits(8)
val write_byte : (address, bits(8)) -> unit

function read_word(addr : address) -> bits(16) = {
  // TODO: alignment?  overflow?
  read_byte(addr) @ read_byte(addr + 0x00001)
}

function write_word(addr : address, w : bits(16)) -> unit = {
  // TODO: alignment?  overflow?
  write_byte(addr, w[15..8]);
  write_byte(addr + 0x00001, w[7..0])
}

// Totally going to regret using lists
register locals : list(bits(16)) = [||]
register stack : list(bits(16)) = [||]
type stack_frame = (list(bits(16)), list(bits(16)), option(bits(8)), address)
register routine_stack : list(stack_frame) = [||]

function pop() -> bits(16) = {
  match stack {
    [||] => throw StackUnderflow(),
    h::t => {
      stack = t;
      h
    }
  }
}

function push(w : bits(16)) -> unit = {
  // TODO: warn when over a reasonable limit?
  stack = w::stack
}

function global_variable_address(v : bits(8)) -> address = {
  let table = read_word(0x0000c);
  sail_zero_extend(table, 20) + sail_zero_extend(v - 0x10, 20);
}

function read_local_variable(vr : bits(8)) -> bits(16) = {
  let i = unsigned(vr - 0x01);
  match nth(locals, i) {
  None() => throw NoSuchLocal(i),
  Some(vl) => vl
  }
}

function read_variable (vr : bits(8)) -> bits(16) = {
  // stack
  if vr == 0x00 then pop()
  // local
  else if vr <_u 0x10 then read_local_variable(vr)
  // global
  else read_word(global_variable_address(vr))
}

function write_local_variable(vr : bits(8), vl : bits(16)) -> unit = {
  let i = unsigned(vr - 0x01);
  match set_nth(locals, i, vl) {
  None() => throw NoSuchLocal(i),
  Some(l) => locals = l
  }
} 

function write_variable(vr : bits(8), vl : bits(16)) -> unit = {
  if vr == 0x00 then push(vl)
  else if vr <_u 0x10 then write_local_variable(vr, vl)
  else write_word(global_variable_address(vr), vl)
}

function routine_offset() -> address = sail_zero_extend(read_word(0x00028), 20)
function strings_offset() -> address = sail_zero_extend(read_word(0x0002a), 20)

enum pack_type = {PackCall, PackPrint}

function unpack_address(w : bits(16), t : pack_type) -> address = {
  let w = sail_zero_extend(w, 20);
  if version <= 3 then w << 1
  else if version <= 5 then w << 2
  else if version <= 7 then match t {
    PackCall  => w << 2 + routine_offset(),
    PackPrint => w << 2 + strings_offset(),
  }
  else w << 3
}
