use isla_lib::{
    bitvector::b64::B64,
    executor::path_cache::{CachedPath, NameEnvironment, PathValidator, Segment},
};

pub fn validate_cache(
    segments: &[Segment<B64>],
    paths: &[CachedPath<B64>],
    names: &NameEnvironment,
    pma: &[(String, u32)],
) {
    let mut validator = PathValidator::new(names, &[], pma);
    for segment in segments.iter().cloned() {
        validator.segment(&segment.into());
    }
    for path in paths {
        validator.path(path);
    }
}
