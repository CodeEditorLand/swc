use swc_common::{
	FileName,
	SourceMap,
	errors::{ColorConfig, Handler},
	sync::Lrc,
};
use swc_ecma_parser::{Capturing, Parser, StringInput, Syntax, lexer::Lexer};

fn main() {
	let cm:Lrc<SourceMap> = Default::default();

	let handler = Handler::with_tty_emitter(ColorConfig::Auto, true, false, Some(cm.clone()));

	// Real usage
	// let fm = cm
	//     .load_file(Path::new("test.js"))
	//     .expect("failed to load test.js");

	let fm =
		cm.new_source_file(FileName::Custom("test.js".into()).into(), "function foo() {}".into());

	let lexer = Lexer::new(
		Syntax::Es(Default::default()),
		Default::default(),
		StringInput::from(&*fm),
		None,
	);

	let capturing = Capturing::new(lexer);

	let mut parser = Parser::new_from(capturing);

	for e in parser.take_errors() {
		e.into_diagnostic(&handler).emit();
	}

	let _module = parser
		.parse_module()
		.map_err(|e| e.into_diagnostic(&handler).emit())
		.expect("Failed to parse module.");

	println!("Tokens: {:?}", parser.input().take());

	let cm:Lrc<SourceMap> = Default::default();

	let handler = Handler::with_tty_emitter(ColorConfig::Auto, true, false, Some(cm.clone()));

	// Real usage
	// let fm = cm
	//     .load_file(Path::new("test.js"))
	//     .expect("failed to load test.js");

	let fm =
		cm.new_source_file(FileName::Custom("test.js".into()).into(), "function foo() {}".into());

	let lexer = Lexer::new(
		Syntax::Es(Default::default()),
		Default::default(),
		StringInput::from(&*fm),
		None,
	);

	let capturing = Capturing::new(lexer);

	let mut parser = Parser::new_from(capturing);

	for e in parser.take_errors() {
		e.into_diagnostic(&handler).emit();
	}

	let _module = parser
		.parse_module()
		.map_err(|e| e.into_diagnostic(&handler).emit())
		.expect("Failed to parse module.");

	println!("Tokens: {:?}", parser.input().take());
}
