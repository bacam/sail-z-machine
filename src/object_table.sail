function object_addr(object : bits(16)) -> address = {
  let (defaults, object_size) : (int, int) = if version <= 3 then (62, 9) else (126, 14);
  add_bits_int(object_table(), defaults + object_size * (unsigned(object) - 1))
}

function test_attribute(object : bits(16), attribute : bits(16)) -> bool = {
  let addr = object_addr(object);
  if attribute >_s (if version <= 3 then 0x0020 else 0x0040) then throw BadAttribute(object, attribute);
  let offset = unsigned(attribute >> 3);
  let byte = read_byte(add_bits_int(addr, offset));
  byte[unsigned(attribute[2..0])] == bitone
}

function set_attribute(object : bits(16), attribute : bits(16)) -> unit = {
  let addr = object_addr(object);
  if attribute >_s (if version <= 3 then 0x0020 else 0x0040) then throw BadAttribute(object, attribute);
  let offset = unsigned(attribute >> 3);
  let byte_addr = add_bits_int(addr, offset);
  var byte = read_byte(byte_addr);
  byte[unsigned(attribute[2..0])] = bitone;
  write_byte(byte_addr, byte)
}

function object_parent(object : bits(16)) -> bits(16) = {
  if version <= 3 then sail_zero_extend(read_byte(object_addr(object) + 0x00004), 16)
  else read_word(object_addr(object) + 0x00006)
}

function object_sibling(object : bits(16)) -> bits(16) = {
  if version <= 3 then sail_zero_extend(read_byte(object_addr(object) + 0x00005), 16)
  else read_word(object_addr(object) + 0x00008)
}

function object_child(object : bits(16)) -> bits(16) = {
  if version <= 3 then sail_zero_extend(read_byte(object_addr(object) + 0x00006), 16)
  else read_word(object_addr(object) + 0x0000a)
}

function object_properties(object : bits(16)) -> address = {
  if version <= 3 then sail_zero_extend(read_word(object_addr(object) + 0x00007), 20)
  else sail_zero_extend(read_word(object_addr(object) + 0x0000c), 20)
}

function set_object_parent(object : bits(16), parent : bits(16)) -> unit = {
  if version <= 3 then write_byte(object_addr(object) + 0x00004, truncate(parent, 8))
  else write_word(object_addr(object) + 0x00006, parent)
}

function set_object_sibling(object : bits(16), sibling : bits(16)) -> unit = {
  if version <= 3 then write_byte(object_addr(object) + 0x00005, truncate(sibling, 8))
  else write_word(object_addr(object) + 0x00008, sibling)
}

function set_object_child(object : bits(16), child : bits(16)) -> unit = {
  if version <= 3 then write_byte(object_addr(object) + 0x00006, truncate(child, 8))
  else write_word(object_addr(object) + 0x0000a, child)
}

function read_property_size_bytes(addr : address) -> (bool, address, int, int) = {
  if version <= 3 then {
    let b = read_byte(addr);
    (b != 0x00, addr + 0x00001, unsigned(b[7..5]) + 1, unsigned(b[4..0]))
  } else {
    let b = read_byte(addr);
    if b[7] == bitzero then (b != 0x00, addr + 0x00001, unsigned(b[6..6]) + 1, unsigned(b[5..0])) else {
      let b' = read_byte(addr + 0x00001);
      (true, addr + 0x00002, unsigned(b'[5..0]), unsigned(b[5..0]))
    }
  }
}

// TODO: version >= 4
function get_property_address(object : bits(16), property : bits(16), use_default : bool) -> (address, int) = {
  let property_number = unsigned(property);
  let base_addr = object_properties(object);
  var prop_ptr = base_addr + sail_zero_extend(read_byte(base_addr), 20) << 1 + 1;
  var is_prop : bool = false;
  var size : int = 0;
  var number : int = 0;
  (is_prop, prop_ptr, size, number) = read_property_size_bytes(prop_ptr);
  while is_prop & number != property_number do {
    prop_ptr = prop_ptr + size;
    (is_prop, prop_ptr, size, number) = read_property_size_bytes(prop_ptr);
  };
  if number != property_number then {
    if use_default
    then (object_table() + sail_zero_extend(property, 20) << 1, 2)
    else throw PropertyNotFound(object, property);
  } else (prop_ptr, size)
}

function get_property(object : bits(16), property : bits(16)) -> bits(16) = {
  let (prop_addr, size) = get_property_address(object, property, true);
  match size {
  // The get_prop instruction spec doesn't say if it's signed, but set_prop is
  1 => sail_sign_extend(read_byte(prop_addr), 16),
  2 => read_word(prop_addr),
  _ => throw WrongPropertySize(object, property),
  }
}

function set_property(object : bits(16), property : bits(16), value : bits(16)) -> unit = {
  let (prop_addr, size) = get_property_address(object, property, false);
  match size {
  1 => write_byte(prop_addr, truncate(value, 8)),
  2 => write_word(prop_addr, value),
  _ => throw WrongPropertySize(object, property),
  }
}
