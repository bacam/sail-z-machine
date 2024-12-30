$include <concurrency_interface/read_write.sail>

function extend_address(a : address) -> bits(32) = sail_zero_extend(a, 32)

instantiation sail_mem_read with
  'pa = address,
  pa_bits = extend_address,
  'translation_summary = unit,
  'arch_ak = unit,
  'abort = unit

instantiation sail_mem_write with
  pa_bits = extend_address

function read_byte(addr) = {
  let req : Mem_read_request(1, 20, bits(20), unit, unit) = struct {
    access_kind = AK_arch (), // No access kinds here
    va = None(), // No virtual memory here
    pa = addr,
    translation = (),
    size = 1,
    tag = false
  };
  match sail_mem_read(req) {
  Ok((v, _)) => v,
  Err() => unreachable("memory read failed")
  }
}

function write_byte(addr, byte) = {
  let req : Mem_write_request(1, 20, bits(20), unit, unit) = struct {
    access_kind = AK_arch (), // No access kinds here
    va = None(), // No virtual memory here
    pa = addr,
    translation = (),
    size = 1,
    value = Some(byte),
    tag = None()
  };
  match sail_mem_write(req) {
  Ok(_) => (),
  Err() => unreachable("memory write failed")
  }
}
