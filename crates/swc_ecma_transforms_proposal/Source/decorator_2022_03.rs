use swc_ecma_ast::Pass;

use crate::{DecoratorVersion, decorator_impl::decorator_impl};

pub fn decorator_2022_03() -> impl Pass { decorator_impl(DecoratorVersion::V202203) }
