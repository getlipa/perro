//! Error enum with helper functions.
//!
//! # Examples
//!
//! ```ignore
//! fn foo(x: u32) -> Result<String, Error<RuntimeErrorCode>> {
//!     if x <= 10 {
//!         return Err(invalid_input("x must be greater than 10"));
//!     }
//!     foreign_function().map_to_runtime_error("Foreign code failed")?;
//!     internal_function().prefix_error("Internal function failed")?;
//!     another_internal_function().lift_invalid_input("Another failure")?;
//! }
//! ```

use std::fmt::{Debug, Display};

#[derive(Debug, PartialEq, Eq, thiserror::Error)]
pub enum Error<C> {
    /// Invalid input.
    /// Consider fixing the input and retrying the request.
    #[error("InvalidInput: {msg}")]
    InvalidInput { msg: String },

    /// Recoverable problem (e.g. network issue, problem with en external service).
    /// Consider retrying the request.
    #[error("RuntimeError: {code} - {msg}")]
    RuntimeError { code: C, msg: String },

    /// Unrecoverable problem (e.g. internal invariant broken).
    /// Consider suggesting the user to report the issue to the developers.
    #[error("PermanentFailure: {msg}")]
    PermanentFailure { msg: String },
}

pub fn invalid_input<E: ToString, C: Display + Debug + Eq>(e: E) -> Error<C> {
    Error::InvalidInput { msg: e.to_string() }
}

pub fn runtime_error<E: ToString, C: Display + Debug + Eq>(code: C, e: E) -> Error<C> {
    Error::RuntimeError {
        code,
        msg: e.to_string(),
    }
}

pub fn permanent_failure<E: ToString, C: Display + Debug + Eq>(e: E) -> Error<C> {
    Error::PermanentFailure { msg: e.to_string() }
}

pub trait ResultTrait<T, C> {
    /// Lift `InvalidInput` error into `PermanentFailure`.
    ///
    /// Use the method when you want to propagate an error from an internal
    /// function to the caller.
    /// Reasoning is that if you got `InvalidInput` it means you failed to
    /// validate the input for the internal function yourself, so for you it
    /// becomes `PermanentFailure`.
    fn lift_invalid_input(self) -> Result<T, Error<C>>;

    fn prefix_error<M: ToString + 'static>(self, msg: M) -> Result<T, Error<C>>;
}

impl<T, C> ResultTrait<T, C> for Result<T, Error<C>> {
    fn lift_invalid_input(self) -> Result<T, Error<C>> {
        self.map_err(|e| match e {
            Error::InvalidInput { msg } => Error::PermanentFailure {
                msg: format!("InvalidInput: {msg}"),
            },
            another_error => another_error,
        })
    }

    fn prefix_error<M: ToString + 'static>(self, prefix: M) -> Result<T, Error<C>> {
        self.map_err(|e| match e {
            Error::InvalidInput { msg } => Error::InvalidInput {
                msg: format!("{}: {}", prefix.to_string(), msg),
            },
            Error::RuntimeError { code, msg } => Error::RuntimeError {
                code,
                msg: format!("{}: {}", prefix.to_string(), msg),
            },
            Error::PermanentFailure { msg } => Error::PermanentFailure {
                msg: format!("{}: {}", prefix.to_string(), msg),
            },
        })
    }
}

pub trait MapToError<T, E: ToString, C> {
    fn map_to_invalid_input<M: ToString>(self, msg: M) -> Result<T, Error<C>>;
    fn map_to_runtime_error<M: ToString>(self, code: C, msg: M) -> Result<T, Error<C>>;
    fn map_to_permanent_failure<M: ToString>(self, msg: M) -> Result<T, Error<C>>;
}

impl<T, E: ToString, C> MapToError<T, E, C> for Result<T, E> {
    fn map_to_invalid_input<M: ToString>(self, msg: M) -> Result<T, Error<C>> {
        self.map_err(move |e| Error::InvalidInput {
            msg: format!("{}: {}", msg.to_string(), e.to_string()),
        })
    }

    fn map_to_runtime_error<M: ToString>(self, code: C, msg: M) -> Result<T, Error<C>> {
        self.map_err(move |e| Error::RuntimeError {
            code,
            msg: format!("{}: {}", msg.to_string(), e.to_string()),
        })
    }

    fn map_to_permanent_failure<M: ToString>(self, msg: M) -> Result<T, Error<C>> {
        self.map_err(move |e| Error::PermanentFailure {
            msg: format!("{}: {}", msg.to_string(), e.to_string()),
        })
    }
}

pub trait MapToErrorForUnitType<T, C> {
    fn map_to_invalid_input<M: ToString>(self, msg: M) -> Result<T, Error<C>>;
    fn map_to_runtime_error<M: ToString>(self, code: C, msg: M) -> Result<T, Error<C>>;
    fn map_to_permanent_failure<M: ToString>(self, msg: M) -> Result<T, Error<C>>;
}

impl<T, C> MapToErrorForUnitType<T, C> for Result<T, ()> {
    fn map_to_invalid_input<M: ToString>(self, msg: M) -> Result<T, Error<C>> {
        self.map_err(move |()| Error::InvalidInput {
            msg: msg.to_string(),
        })
    }

    fn map_to_runtime_error<M: ToString>(self, code: C, msg: M) -> Result<T, Error<C>> {
        self.map_err(move |()| Error::RuntimeError {
            code,
            msg: msg.to_string(),
        })
    }

    fn map_to_permanent_failure<M: ToString>(self, msg: M) -> Result<T, Error<C>> {
        self.map_err(move |()| Error::PermanentFailure {
            msg: msg.to_string(),
        })
    }
}

pub trait OptionToError<T> {
    fn ok_or_invalid_input<M: ToString, C: Display + Debug + Eq>(
        self,
        msg: M,
    ) -> Result<T, Error<C>>;
    fn ok_or_runtime_error<M: ToString, C: Display + Debug + Eq>(
        self,
        code: C,
        msg: M,
    ) -> Result<T, Error<C>>;
    fn ok_or_permanent_failure<M: ToString, C: Display + Debug + Eq>(
        self,
        msg: M,
    ) -> Result<T, Error<C>>;
}

impl<T> OptionToError<T> for Option<T> {
    fn ok_or_invalid_input<M: ToString, C: Display + Debug + Eq>(
        self,
        msg: M,
    ) -> Result<T, Error<C>> {
        self.ok_or_else(|| invalid_input(msg))
    }

    fn ok_or_runtime_error<M: ToString, C: Display + Debug + Eq>(
        self,
        code: C,
        msg: M,
    ) -> Result<T, Error<C>> {
        self.ok_or_else(|| runtime_error(code, msg))
    }

    fn ok_or_permanent_failure<M: ToString, C: Display + Debug + Eq>(
        self,
        msg: M,
    ) -> Result<T, Error<C>> {
        self.ok_or_else(|| permanent_failure(msg))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fmt::{Display, Formatter};

    #[derive(Debug, PartialEq, Eq)]
    pub enum TestRuntimeErrorCode {
        RemoteServiceUnavailable,
    }

    impl Display for TestRuntimeErrorCode {
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            write!(f, "{self:?}")
        }
    }

    #[test]
    fn test_map_to_lipa_errors() {
        use std::io::{Error, ErrorKind};

        let io_error: std::io::Result<()> = Err(Error::new(ErrorKind::Other, "File not found"));
        let lipa_error = io_error
            .map_to_runtime_error(TestRuntimeErrorCode::RemoteServiceUnavailable, "No backup")
            .unwrap_err();
        assert_eq!(
            lipa_error.to_string(),
            "RuntimeError: RemoteServiceUnavailable - No backup: File not found"
        );

        let error: Result<(), ()> = Err(());
        let lipa_error = error
            .map_to_runtime_error(TestRuntimeErrorCode::RemoteServiceUnavailable, "No backup")
            .unwrap_err();
        assert_eq!(
            lipa_error.to_string(),
            "RuntimeError: RemoteServiceUnavailable - No backup"
        );
    }

    #[test]
    fn test_lift_invalid_input() {
        let result: Result<(), Error<TestRuntimeErrorCode>> =
            Err(invalid_input("Number must be positive")).lift_invalid_input();
        assert_eq!(
            result.unwrap_err().to_string(),
            "PermanentFailure: InvalidInput: Number must be positive"
        );

        let result: Result<(), Error<TestRuntimeErrorCode>> = Err(runtime_error(
            TestRuntimeErrorCode::RemoteServiceUnavailable,
            "Socket timeout",
        ))
        .lift_invalid_input();
        assert_eq!(
            result.unwrap_err().to_string(),
            "RuntimeError: RemoteServiceUnavailable - Socket timeout"
        );

        let result: Result<(), Error<TestRuntimeErrorCode>> =
            Err(permanent_failure("Devision by zero")).lift_invalid_input();
        assert_eq!(
            result.unwrap_err().to_string(),
            "PermanentFailure: Devision by zero"
        );
    }

    #[test]
    fn test_prefix_error() {
        let result: Result<(), Error<TestRuntimeErrorCode>> =
            Err(invalid_input("Number must be positive")).prefix_error("Invalid amount");
        assert_eq!(
            result.unwrap_err().to_string(),
            "InvalidInput: Invalid amount: Number must be positive"
        );
    }

    #[test]
    fn test_ok_or() {
        assert_eq!(
            Some(1).ok_or_permanent_failure::<_, TestRuntimeErrorCode>("Value expected"),
            Ok(1)
        );

        let none: Option<u32> = None;

        let error = none
            .ok_or_invalid_input::<_, TestRuntimeErrorCode>("Value expected")
            .unwrap_err();
        assert_eq!(error.to_string(), "InvalidInput: Value expected");

        let error = none
            .ok_or_runtime_error::<_, TestRuntimeErrorCode>(
                TestRuntimeErrorCode::RemoteServiceUnavailable,
                "Value expected",
            )
            .unwrap_err();
        assert_eq!(
            error.to_string(),
            "RuntimeError: RemoteServiceUnavailable - Value expected"
        );

        let error = none
            .ok_or_permanent_failure::<_, TestRuntimeErrorCode>("Value expected")
            .unwrap_err();
        assert_eq!(error.to_string(), "PermanentFailure: Value expected");
    }
}
