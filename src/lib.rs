//! Utilities for working with *Inhabited Zero-Sized Types*,
//! or, as referred to in this crate, **IZSTs**.

#![no_std]

use ::core::{
	any::type_name,
	fmt,
	marker::PhantomData,
	ptr::NonNull,
};

macro_rules! check_zst {
	($t:ty) => {
		if size_of::<$t>() != 0 {
			panic!(concat!("`", stringify!($t), "` must be zero-sized"));
		}
	};
}
macro_rules! check_zst_2 {
	($t:ty) => {{
		const { check_zst!($t) }
		check_zst!($t)
	}};
}

/// Trait for creating [`IZstProvider`]s from references to inhabited types.
/// 
/// Currently, Rust provides no mechanism of distinguishing inhabited and zero-sized types,
/// so this type is implemented for all `T: 'static`.
/// However, users should instead use a `T: MaybeZst` bound.
pub trait MaybeZst: Sized + 'static {
	/// Returns an [`IZstProvider`] for `self`,
	/// panicking either at run-time or compile-time if the type isn't zero-sized.
	fn izst_provider(&self) -> IZstProvider<Self> {
		check_zst_2!(Self);
		unsafe { IZstProvider::new_unchecked() }
	}

	/// Returns an [`IZstProvider`] for `self`,
	/// or `None` if the type isn't zero-sized.
	fn try_izst_provider(&self) -> Option<IZstProvider<Self>> {
		unsafe { IZstProvider::try_new_inhabited() }
	}
}
impl<T: 'static> MaybeZst for T {}

/// Provider of inhabited, zero-sized types.
/// 
/// # Layout
/// This type is guaranteed to be inhabited and zero-sized itself
/// (however that does not say anything about `T`).
/// As such, it can be used like [`PhantomData`] to add extra information to types without changing their size.
/// 
/// # Examples
/// Wrapping a `fn` item:
/// ```
/// # use izst::IZstProvider;
/// struct Greeter<F: 'static> {
///     greeter_provider: IZstProvider<F>,
/// }
/// 
/// impl<F: 'static + FnMut() -> i32 + Copy> Greeter<F> {
///     pub fn new(greeter_provider: IZstProvider<F>) -> Self {
///         Self {
///             greeter_provider,
///         }
///     }
/// 
///     pub fn greet(&self) -> i32 {
///         self.greeter_provider.provide_copy()()
///     }
/// }
/// 
/// fn greet() -> i32 {
///     println!("Hello, world!");
///     42
/// }
/// 
/// let mut greeter = Greeter::new(IZstProvider::from_inhabited(&greet));
/// assert_eq!(size_of_val(&greeter), 0);
/// assert_eq!(greeter.greet(), 42);
/// ```
#[repr(transparent)]
pub struct IZstProvider<T: 'static>(PhantomData<fn() -> T>);
impl<T: 'static> IZstProvider<T> {
	/// Returns an Inhabited ZST provider,
	/// with proof that `T` is inhabited
	/// given that there is a reference to a value of this type.
	/// 
	/// See also [`try_from_inhabited`](Self::try_from_inhabited) for the non-panicking version.
	/// 
	/// # Panics
	/// The function may panic either at run-time or compile-time if `T` isn't zero-sized.
	pub const fn from_inhabited(proof: &T) -> Self {
		let _ = proof;
		unsafe { Self::new_inhabited() }
	}

	/// Returns an Inhabited ZST provider,
	/// with proof that `T` is inhabited
	/// given that there is a reference to a value of this type,
	/// or `None` if `T` isn't zero-sized.
	pub const fn try_from_inhabited(proof: &T) -> Option<Self> {
		let _ = proof;
		unsafe { Self::try_new_inhabited() }
	}

	/// Returns an instance of the inhabited zero-sized type `T`.
	/// 
	/// This function requires that `T` is [`Copy`],
	/// so that it has no destructors which may potentially need to be called,
	/// which means that it's more likely that no inner invariants would be violated.
	pub const fn provide_copy(&self) -> T
	where
		T: Copy,
	{
		// SAFETY: `T` is `Copy`, so it likely can't have any invariants associated with it.
		unsafe { self.provide() }
	}

	/// Returns an instance of the inhabited zero-sized type `T`.
	/// 
	/// See also [`provide_copy`](Self::provide_copy) for more information.
	/// 
	/// # Safety
	/// The lifetime `'a` must be valid for a reference to a value of type `T` *and its usages*.
	pub const unsafe fn provide_copy_ref<'a>(&self) -> &'a T
	where
		T: Copy,
	{
		// SAFETY: `T` is `Copy`, so it likely can't have any invariants associated with it.
		unsafe { self.provide_ref() }
	}

	/// Returns an instance of the inhabited zero-sized type `T`.
	/// 
	/// See also [`provide_copy`](Self::provide_copy) for more information.
	/// 
	/// # Safety
	/// The lifetime `'a` must be valid for a reference to a value of type `T` *and its usages*.
	pub const unsafe fn provide_copy_mut<'a>(&self) -> &'a mut T
	where
		T: Copy,
	{
		// SAFETY: `T` is `Copy`, so it likely can't have any invariants associated with it.
		unsafe { self.provide_mut() }
	}

	/// Returns an instance of the inhabited zero-sized type `T`.
	/// 
	/// # Safety
	/// If `T` is [`Drop`], then it may potentially be unsound to construct instances of it,
	/// as it may violate some inner invariant of the type.
	/// The caller must ensure that this is the case, or use [`provide_copy`](Self::provide_copy).
	pub const unsafe fn provide(&self) -> T {
		// SAFETY: `T` is zero-sized and inhabited, as per the invariant.
		unsafe { NonNull::<T>::dangling().read() }
	}

	/// Returns a reference to a value of the inhabited zero-sized type `T`.
	/// 
	/// # Safety
	/// The lifetime `'a` must be valid for a reference to a value of type `T`.
	/// 
	/// See also [`provide`](Self::provide) for more safety information.
	pub const unsafe fn provide_ref<'a>(&self) -> &'a T {
		// SAFETY: `T` is zero-sized and inhabited, as per the invariant.
		unsafe { NonNull::<T>::dangling().as_ref() }
	}

	/// Returns a reference to a value of the inhabited zero-sized type `T`.
	/// 
	/// # Safety
	/// The lifetime `'a` must be valid for a reference to a value of type `T`.
	/// 
	/// See also [`provide`](Self::provide) for more safety information.
	pub const unsafe fn provide_mut<'a>(&self) -> &'a mut T {
		// SAFETY: `T` is zero-sized and inhabited, as per the invariant.
		unsafe { NonNull::<T>::dangling().as_mut() }
	}

	/// Returns an Inhabited ZST provider,
	/// checking whether `T` is zero-sized.
	/// 
	/// # Safety
	/// As it is currently not possible to check if a type is inhabited in stable Rust,
	/// the caller must guarantee that `T` is, indeed, inhabited;
	/// that is, it may *not* be a type like [`Infallible`](::core::convert::Infallible),
	/// which can never have a value.
	/// 
	/// `T` must also have no inner *invariants*;
	/// that is, various "proof" types which prove something at compile time (such as this type!)
	/// *must not* be used.
	/// For example, it is invalid to provide [`IZstProvider`]s for a `T` which isn't inhabited, or isn't a ZST:
	/// ```no_run
	/// # use izst::IZstProvider;
	/// type NotAnIZst = usize;
	/// type NotAnIZstProvider = IZstProvider<NotAnIZst>;
	/// 
	/// // This is Undefined Behavior.
	/// // `NotAnIZstProvider` is an IZST itself, so the `.unwrap()` succeeds.
	/// const UB_PROVIDER: IZstProvider<NotAnIZstProvider> = unsafe { IZstProvider::try_new_inhabited().unwrap() };
	/// 
	/// // Using `UB_PROVIDER` is also Undefined Behavior.
	/// let not_an_izst: NotAnIZst = UB_PROVIDER.provide_copy().provide_copy();
	/// ```
	pub const unsafe fn try_new_inhabited() -> Option<Self> {
		if size_of::<T>() == 0 {
			Some(unsafe { Self::new_unchecked() })
		} else {
			None
		}
	}

	/// Returns an Inhabited ZST provider.
	/// 
	/// As it is currently not possible to check if a type is inhabited in stable Rust,
	/// the caller must guarantee that `T` is, indeed, inhabited.
	/// This means that `T`, for instance, may *not* be a type like [`Infallible`](::core::convert::Infallible),
	/// which can never have a value.
	/// 
	/// # Panics
	/// The function may panic either at run-time or compile-time if `T` isn't zero-sized.
	/// 
	/// # Safety
	/// `T` must be inhabited,
	/// and have no inner *invariants* -
	/// see [`try_new_inhabited`](Self::try_new_inhabited) for more information.
	pub const unsafe fn new_inhabited() -> Self {
		check_zst_2!(T);
		unsafe { Self::new_unchecked() }
	}

	/// Returns an Inhabited ZST provider without doing any safety checks.
	/// 
	/// # Safety
	/// `T` must be zero-sized, inhabited,
	/// and have no inner *invariants* -
	/// see [`try_new_inhabited`](Self::try_new_inhabited) for more information.
	pub const unsafe fn new_unchecked() -> Self {
		Self(PhantomData)
	}
}

impl<T: 'static> fmt::Debug for IZstProvider<T> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		f.write_str("IZstProvider -> ")?;
		f.write_str(type_name::<T>())
	}
}
impl<T: 'static> Clone for IZstProvider<T> {
	fn clone(&self) -> Self {
		*self
	}
}
impl<T: 'static> Copy for IZstProvider<T> {}

impl<T: 'static> From<&T> for IZstProvider<T> {
	fn from(value: &T) -> Self {
		Self::from_inhabited(value)
	}
}

impl<T: 'static> From<T> for IZstProvider<T> {
	fn from(value: T) -> Self {
		Self::from_inhabited(&value)
	}
}

