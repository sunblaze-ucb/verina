"""ITP registration module.

This module handles the registration of all ITP implementations
when the verina package is loaded.
"""

_registered = False


def register_all_itps():
    """Register all available ITP implementations.

    This function is idempotent - calling it multiple times has no effect
    after the first call.
    """
    global _registered
    if _registered:
        return

    # Import and register Lean
    try:
        from verina.lean import _register_lean
        _register_lean()
    except ImportError as e:
        import warnings
        warnings.warn(f"Failed to register Lean ITP: {e}")

    # Import and register Coq
    try:
        from verina.coq import _register_coq
        _register_coq()
    except ImportError as e:
        import warnings
        warnings.warn(f"Failed to register Coq ITP: {e}")

    _registered = True


def ensure_itps_registered():
    """Ensure ITPs are registered before use.

    Call this function before using any ITP functionality to ensure
    all implementations are available.
    """
    register_all_itps()
