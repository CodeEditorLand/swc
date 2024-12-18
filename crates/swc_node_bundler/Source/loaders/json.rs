use std::sync::Arc;

use anyhow::{Error, anyhow};
use swc_common::{DUMMY_SP, SourceFile};
use swc_ecma_ast::*;
use swc_ecma_parser::{Syntax, parse_file_as_expr};

pub(super) fn load_json_as_module(fm:&Arc<SourceFile>) -> Result<Module, Error> {
	let expr = parse_file_as_expr(fm, Syntax::default(), EsVersion::Es2020, None, &mut Vec::new())
		.map_err(|err| anyhow!("failed parse json as javascript object: {:#?}", err))?;

	let export = ExprStmt {
		span:DUMMY_SP,
		expr:AssignExpr {
			span:DUMMY_SP,
			op:op!("="),
			left:MemberExpr {
				span:DUMMY_SP,
				obj:Box::new(Ident::new_no_ctxt("module".into(), DUMMY_SP).into()),
				prop:MemberProp::Ident(IdentName::new("exports".into(), DUMMY_SP)),
			}
			.into(),
			right:expr,
		}
		.into(),
	}
	.into();

	Ok(Module { span:DUMMY_SP, body:vec![export], shebang:None })
}
