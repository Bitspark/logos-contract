use logos_contract::parse_hash_hex;

#[test]
fn canonical_hash_text_reads_exact_octets() {
    let canonical = "01ab".repeat(16);
    let hash = parse_hash_hex(canonical.as_bytes()).expect("canonical hash");
    for pair in hash.as_chunks::<2>().0 {
        assert_eq!(*pair, [1, 0xab]);
    }
    assert_eq!(parse_hash_hex("00".repeat(32).as_bytes()), Some([0; 32]));
    for text in [
        format!("fg{}", &canonical[2..]),
        canonical[2..].to_owned(),
        format!("{canonical}0f"),
        canonical.to_uppercase(),
    ] {
        assert_eq!(parse_hash_hex(text.as_bytes()), None, "{text}");
    }
}
