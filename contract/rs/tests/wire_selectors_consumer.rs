use logos_contract::{cert_wire_spans, cert_wire_spans_at, PathStep};

#[test]
fn invalid_selector_counts_precede_frame_traversal() {
    for index in [1u64 << 53, (1u64 << 53) + 1, u64::MAX] {
        for frame in [&[1u8, 0][..], &[1, 1, 1, 0][..], &[][..]] {
            let failure = cert_wire_spans(frame, &[index]).expect_err("invalid selector");
            assert_eq!(failure.name(), "invalid_path");
            for steps in [
                vec![PathStep::Index(index)],
                vec![PathStep::Each, PathStep::Index(index)],
                vec![PathStep::Index(99), PathStep::Index(index)],
            ] {
                let failure = cert_wire_spans_at(frame, &steps).expect_err("invalid selector");
                assert_eq!(failure.name(), "invalid_path");
            }
        }
    }
}

#[test]
fn absent_slots_and_selected_coordinates_are_independent_of_layout() {
    let frame = [
        1, 2, 0, 3, b't', b'a', b'g', 1, 2, 1, 2, 1, 0, 1, 1, 0, 1, b'a', 1, 2, 1, 0, 1, 1, 0, 2,
        b'b', b'c',
    ];
    for index in [
        2,
        (1 << 31) - 1,
        1 << 31,
        (1 << 32) - 1,
        1 << 32,
        (1 << 53) - 1,
    ] {
        assert_eq!(cert_wire_spans(&frame, &[index]), Ok(vec![]));
        assert_eq!(
            cert_wire_spans_at(&frame, &[PathStep::Index(index)]),
            Ok(vec![])
        );
        assert_eq!(PathStep::Index(index).index(), Some(index));
    }
    assert_eq!(PathStep::Index(0).index(), Some(0));
    assert_eq!(PathStep::Each.index(), None);
    let spans = cert_wire_spans_at(
        &frame,
        &[PathStep::Index(1), PathStep::Each, PathStep::Index(1)],
    )
    .expect("consumer-authored selector");
    assert_eq!(spans.len(), 2);
    assert_eq!(spans[0].path, vec![1, 0, 1, 0]);
    assert_eq!(spans[1].path, vec![1, 1, 1, 0]);
    for (span, expected) in spans
        .iter()
        .zip([&[0, 1, b'a'][..], &[0, 2, b'b', b'c'][..]])
    {
        assert_eq!(&frame[span.start..span.start + span.span], expected);
    }
}
