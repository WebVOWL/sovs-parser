use criterion::{Bencher, Criterion, criterion_group, criterion_main};
use sovs_parser::Specification;

fn bench_isomorphism(b: &mut Bencher, sa: &str, sb: &str) {
    let sa = Specification::parse(sa).expect("spec A should parse");
    let sb = Specification::parse(sb).expect("spec B should parse");
    b.iter(|| sa.is_isomorphic_to(&sb));
}

fn isomorphisms(c: &mut Criterion) {
    let mut g = c.benchmark_group("isomorphism");
    g.throughput(criterion::Throughput::Elements(1));
    g.bench_function("chain_with_in", |b| {
        bench_isomorphism(
            b,
            r"
                node a {}
                node b {}
                node c {}
                node d {}
                node e {}
                edge e1 from a to b {}
                edge e2 from b to c {}
                edge e3 from c to d {}
                edge e4 from e to b {}
                ",
            r"
                node a {}
                node b {}
                node c {}
                node d {}
                node e {}
                edge e1 from a to b {}
                edge e2 from b to c {}
                edge e3 from c to d {}
                edge e4 from e to c {}
                ",
        );
    });
}

criterion_group!(benches, isomorphisms);
criterion_main!(benches);
