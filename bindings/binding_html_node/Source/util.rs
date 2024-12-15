use anyhow::{Error, anyhow};
use swc_common::{FilePathMapping, SourceMap, errors::Handler, sync::Lrc};
use swc_error_reporters::handler::{HandlerOpts, try_with_handler};

pub fn try_with<F, Ret>(op:F) -> Result<Ret, Error>
where
	F: FnOnce(&Lrc<SourceMap>, &Handler) -> Result<Ret, Error>, {
	let cm = Lrc::new(SourceMap::new(FilePathMapping::empty()));

	try_with_handler(
		cm.clone(),
		HandlerOpts { skip_filename:false, ..Default::default() },
		|handler| {
			//
			let result =
				std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| op(&cm, handler)));

			let p = match result {
				Ok(v) => return v,
				Err(v) => v,
			};

			if let Some(s) = p.downcast_ref::<String>() {
				Err(anyhow!("failed to handle: {}", s))
			} else if let Some(s) = p.downcast_ref::<&str>() {
				Err(anyhow!("failed to handle: {}", s))
			} else {
				Err(anyhow!("failed to handle with unknown panic message"))
			}
		},
	)
}
