use std::ops::Deref;

use once_cell::sync::OnceCell;

/// Wrapper for [OnceCell] with support for [rkyv].
#[derive(Clone, Debug)]
pub struct CacheCell<T>(OnceCell<T>);

impl<T> Deref for CacheCell<T> {
    type Target = OnceCell<T>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> CacheCell<T> {
    pub fn new() -> Self {
        Self(OnceCell::new())
    }
}

impl<T> From<T> for CacheCell<T> {
    fn from(value: T) -> Self {
        Self(OnceCell::from(value))
    }
}

impl<T> Default for CacheCell<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(feature = "rkyv-impl")]
mod rkyv_impl {
    use std::{hint::unreachable_unchecked, ptr};

    use rkyv::{
        option::ArchivedOption, out_field, Archive, Archived, Deserialize, Fallible, Resolver,
    use std::hint::unreachable_unchecked;

    use rancor::Fallible;
    use rkyv::{
        munge::munge, option::ArchivedOption, traits::NoUndef, Archive, Deserialize, Place,
        Serialize,
    };

    use super::*;

    #[allow(dead_code)]
    #[repr(u8)]
    enum ArchivedOptionTag {
        None,
        Some,
    }

    // SAFETY: `ArchivedOptionTag` is `repr(u8)` and so always consists of a single
    // well-defined byte.
    unsafe impl NoUndef for ArchivedOptionTag {}

    #[repr(C)]
    struct ArchivedOptionVariantNone(ArchivedOptionTag);

    #[repr(C)]
    struct ArchivedOptionVariantSome<T>(ArchivedOptionTag, T);

    impl<T> Archive for CacheCell<T>
    where
        T: Archive,
    {
        type Archived = Archived<Option<T>>;

        type Resolver = Resolver<Option<T>>;

        unsafe fn resolve(&self, pos: usize, resolver: Self::Resolver, out: *mut Self::Archived) {
            match resolver {
                None => {
                    let out = out.cast::<ArchivedOptionVariantNone>();

                    ptr::addr_of_mut!((*out).0).write(ArchivedOptionTag::None);
                }

                Some(resolver) => {
                    let out = out.cast::<ArchivedOptionVariantSome<T::Archived>>();

                    ptr::addr_of_mut!((*out).0).write(ArchivedOptionTag::Some);

                    let v = self.0.get();

                    let value = if let Some(value) = v.as_ref() {
                        value
                    } else {
                        unreachable_unchecked();
                    };

                    let (fp, fo) = out_field!(out.1);

                    value.resolve(pos + fp, resolver, fo);
    impl<T: Archive> Archive for CacheCell<T> {
        type Archived = ArchivedOption<T::Archived>;
        type Resolver = Option<T::Resolver>;

        fn resolve(&self, resolver: Self::Resolver, out: Place<Self::Archived>) {
            match resolver {
                None => {
                    let out = unsafe { out.cast_unchecked::<ArchivedOptionVariantNone>() };
                    munge!(let ArchivedOptionVariantNone(tag) = out);
                    tag.write(ArchivedOptionTag::None);
                }
                Some(resolver) => {
                    let out =
                        unsafe { out.cast_unchecked::<ArchivedOptionVariantSome<T::Archived>>() };
                    munge!(let ArchivedOptionVariantSome(tag, out_value) = out);
                    tag.write(ArchivedOptionTag::Some);

                    let value = if let Some(value) = self.get() {
                        value
                    } else {
                        unsafe {
                            unreachable_unchecked();
                        }
                    };

                    value.resolve(resolver, out_value);
                }
            }
        }
    }

    impl<T: Serialize<S>, S: Fallible + ?Sized> Serialize<S> for CacheCell<T> {
        #[inline]
        fn serialize(&self, serializer: &mut S) -> Result<Self::Resolver, S::Error> {
            self.0
                .get()
        fn serialize(&self, serializer: &mut S) -> Result<Self::Resolver, S::Error> {
            self.get()
                .map(|value| value.serialize(serializer))
                .transpose()
        }
    }

    impl<T: Archive, D: Fallible + ?Sized> Deserialize<CacheCell<T>, D> for ArchivedOption<T::Archived>
    where
        T::Archived: Deserialize<T, D>,
    {
        #[inline]
        fn deserialize(&self, deserializer: &mut D) -> Result<CacheCell<T>, D::Error> {
            match self {
                ArchivedOption::Some(value) => {
                    let v = value.deserialize(deserializer)?;

                    Ok(CacheCell::from(v))
                }

                ArchivedOption::None => Ok(CacheCell::new()),
            }
    impl<T, D> Deserialize<CacheCell<T>, D> for ArchivedOption<T::Archived>
    where
        T: Archive,
        T::Archived: Deserialize<T, D>,
        D: Fallible + ?Sized,
    {
        fn deserialize(&self, deserializer: &mut D) -> Result<CacheCell<T>, D::Error> {
            Ok(match self {
                ArchivedOption::Some(value) => CacheCell::from(value.deserialize(deserializer)?),
                ArchivedOption::None => CacheCell::new(),
            })
        }
    }
}
