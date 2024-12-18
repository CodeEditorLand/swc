#![allow(dead_code)]

use std::io::{Write, stderr};

use swc_common::{SourceMap, SyntaxContext, sync::Lrc};
use swc_ecma_ast::{Ident, Module};
use swc_ecma_codegen::{Emitter, text_writer::JsWriter};
use swc_ecma_visit::{Fold, FoldWith, noop_fold_type};

#[cfg(not(debug_assertions))]
pub(crate) fn print_hygiene(_:&str, _:&Lrc<SourceMap>, _:&Module) {}

#[cfg(debug_assertions)]
pub(crate) fn print_hygiene(event:&str, cm:&Lrc<SourceMap>, t:&Module) {
	let module = t.clone().fold_with(&mut HygieneVisualizer);

	let stdout = stderr();

	let mut w = stdout.lock();

	writeln!(w, "==================== @ {} ====================", event).unwrap();

	Emitter {
		cfg:swc_ecma_codegen::Config::default(),
		cm:cm.clone(),
		comments:None,
		wr:Box::new(JsWriter::new(cm.clone(), "\n", &mut w, None)),
	}
	.emit_module(&module)
	.unwrap();

	writeln!(w, "==================== @ ====================").unwrap();
}

struct HygieneVisualizer;

impl Fold for HygieneVisualizer {
	noop_fold_type!();

	fn fold_ident(&mut self, node:Ident) -> Ident {
		if node.ctxt == SyntaxContext::empty() {
			return node;
		}

		Ident { sym:format!("{}{:?}", node.sym, node.ctxt).into(), ..node }
	}
}
