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
  sorted : bool,
}

function read_dictionary_info(dictionary : address, number_word_separators : nat, user_dictionary : bool) -> dictionary_info = {
  let number_entries = signed(read_word(add_bits_int(dictionary, number_word_separators + 2)));
  let info : dictionary_info = struct {
    entry_length = unsigned(read_byte(add_bits_int(dictionary, number_word_separators + 1))),
    number_entries = abs_int(number_entries),
    entries_start = add_bits_int(dictionary, number_word_separators + 4),
    sorted = not_bool(user_dictionary) | number_entries >= 0,
  };
  if info.entry_length < (if version <= 3 then 4 else 6) then throw InvalidDictionaryEntryLength(info.entry_length);
  info
}

val lookup_entry : forall 'n. (implicit('n), dictionary_info, vector('n, bits(8))) -> option(address)

function lookup_entry(size_zchars, dictionary, zchars) = {
  // We ought to be able to do a binary search here (unless it's an unsorted user dictionary), but keep it simple
  foreach (i from 1 to dictionary.number_entries) {
    let entry = add_bits_int(dictionary.entries_start, i * dictionary.entry_length);
    var found : bool = true;
    foreach (j from 0 to (size_zchars - 1)) {
      found = found & read_byte(add_bits_int(entry, j)) == zchars[j]
    };
    if found then return Some(entry);
  };
  None()
}

function write_entry(word_entry : address, entry : address, letters : int, offset : int) -> unit = {
  write_word(word_entry, truncate(entry, 16));
  write_byte(word_entry + 0x00002, add_bits_int(0x00, letters));
  write_byte(word_entry + 0x00003, add_bits_int(0x00, offset));
}

function tokenise(text : address, total_characters : int, parse : address, dictionary : address, user_dictionary : bool, skip_unrecognised : bool) -> unit = {
  let max_words = unsigned(read_byte(parse));
  let 'number_word_separators = unsigned(read_byte(dictionary));
  var word_separators : vector('number_word_separators + 1, bits(8)) = vector_init(0x32);
  if number_word_separators >= 1 then {
    foreach (i from 1 to number_word_separators) {
      word_separators[i] = read_byte(add_bits_int(dictionary, i))
    }
  };
  let dictionary_info = read_dictionary_info(dictionary, number_word_separators, user_dictionary);

  var j : int = 0;
  var words : int = 0;
  let start_addr = add_bits_int(text, if version < 5 then 1 else 2);
  let 'encode_triplets = if version <= 3 then 2 else 3;
  let empty_entry : vector('encode_triplets * 3, bits(5)) = vector_init(0b00101);

  while words < max_words & j < total_characters do {
    var char = read_byte(add_bits_int(start_addr, j));
    if char == 0x20 then j = j + 1
    else if byte_is_in(word_separators, char) then {
      let (encoded, _) = encode_zscii(empty_entry, 0, char);
      let word_entry = add_bits_int(parse, 2 + 4 * words);
      let dictionary_entry = lookup_entry(dictionary_info, pack_zchars(encoded));
      // TODO: if dictionary_entry >_u 0x0ffff then
      match dictionary_entry {
        Some(e) => write_entry(word_entry, e, 1, j),
	None() if skip_unrecognised => (),
	None() => write_entry(word_entry, 0x00000, 1, j),
      };
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
      let word_entry = add_bits_int(parse, 2 + 4 * words);
      let dictionary_entry = lookup_entry(dictionary_info, pack_zchars(encoded));
      // TODO: if dictionary_entry >_u 0x0ffff then
      match dictionary_entry {
        Some(e) => write_entry(word_entry, e, k, j),
	None() if skip_unrecognised => (),
	None() => write_entry(word_entry, 0x00000, k, j),
      };
      words = words + 1;
      j = j + k;
    }
  };
  write_byte(parse + 0x00001, add_bits_int(0x00, words));
}

