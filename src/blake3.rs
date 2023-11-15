use crate::Aggregate;

use blake3::{Hash, Hasher};

unsafe impl Aggregate for Hash {
    fn aggregate(nodes: &[Self]) -> Self {
        let mut hasher = Hasher::new();
        for node in nodes {
            hasher.update(node.as_bytes());
        }
        hasher.finalize()
    }
}
