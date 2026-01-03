"""ITP (Interactive Theorem Prover) abstraction layer.

This module provides a registry-based abstraction for supporting multiple
theorem provers (Lean, Coq) with a unified interface.

Usage:
    from verina.itp import ITPType, get_compiler, get_parser, get_template_class

    # Get implementations for a specific ITP
    compiler = get_compiler(ITPType.LEAN)
    parser = get_parser(ITPType.LEAN)
    template_class = get_template_class(ITPType.LEAN)
"""

from enum import Enum
from typing import Dict, Type

from verina.itp.base import (
    ITPBenchmarkData,
    ITPBenchmarkDataSection,
    ITPCompiler,
    ITPParser,
    ITPTemplate,
)


class ITPType(str, Enum):
    """Supported Interactive Theorem Prover types."""
    LEAN = "lean"
    COQ = "coq"


# Registry for ITP implementations
_itp_registry: Dict[ITPType, Dict[str, Type]] = {}


def register_itp(
    itp_type: ITPType,
    compiler_class: Type[ITPCompiler],
    parser_class: Type[ITPParser],
    template_class: Type[ITPTemplate],
) -> None:
    """Register an ITP implementation.

    Args:
        itp_type: The ITP type to register.
        compiler_class: Class implementing ITPCompiler.
        parser_class: Class implementing ITPParser.
        template_class: Class implementing ITPTemplate.
    """
    _itp_registry[itp_type] = {
        "compiler": compiler_class,
        "parser": parser_class,
        "template": template_class,
    }


def get_compiler(itp_type: ITPType, **kwargs) -> ITPCompiler:
    """Get a compiler instance for the specified ITP.

    Args:
        itp_type: The ITP type.
        **kwargs: Additional arguments passed to the compiler constructor.
                  For Coq, this can include docker_image='verina-coq'.

    Returns:
        An instance of the ITP's compiler.

    Raises:
        KeyError: If the ITP type is not registered.
    """
    if itp_type not in _itp_registry:
        raise KeyError(f"ITP type '{itp_type}' is not registered. Available: {list(_itp_registry.keys())}")
    return _itp_registry[itp_type]["compiler"](**kwargs)


def get_parser(itp_type: ITPType) -> ITPParser:
    """Get a parser instance for the specified ITP.

    Args:
        itp_type: The ITP type.

    Returns:
        An instance of the ITP's parser.

    Raises:
        KeyError: If the ITP type is not registered.
    """
    if itp_type not in _itp_registry:
        raise KeyError(f"ITP type '{itp_type}' is not registered. Available: {list(_itp_registry.keys())}")
    return _itp_registry[itp_type]["parser"]()


def get_template_class(itp_type: ITPType) -> Type[ITPTemplate]:
    """Get the template class for the specified ITP.

    Args:
        itp_type: The ITP type.

    Returns:
        The ITP's template class (not an instance).

    Raises:
        KeyError: If the ITP type is not registered.
    """
    if itp_type not in _itp_registry:
        raise KeyError(f"ITP type '{itp_type}' is not registered. Available: {list(_itp_registry.keys())}")
    return _itp_registry[itp_type]["template"]


def is_registered(itp_type: ITPType) -> bool:
    """Check if an ITP type is registered.

    Args:
        itp_type: The ITP type to check.

    Returns:
        True if registered, False otherwise.
    """
    return itp_type in _itp_registry


def get_registered_itps() -> list[ITPType]:
    """Get list of all registered ITP types.

    Returns:
        List of registered ITP types.
    """
    return list(_itp_registry.keys())


# Auto-registration function
def _ensure_registered():
    """Ensure all ITPs are registered. Called lazily when needed."""
    from verina.itp.registration import ensure_itps_registered
    ensure_itps_registered()


# Override get_* functions to auto-register on first use
_original_get_compiler = get_compiler
_original_get_parser = get_parser
_original_get_template_class = get_template_class


def get_compiler(itp_type: ITPType, **kwargs) -> ITPCompiler:
    """Get a compiler instance for the specified ITP (auto-registers if needed)."""
    _ensure_registered()
    return _original_get_compiler(itp_type, **kwargs)


def get_parser(itp_type: ITPType) -> ITPParser:
    """Get a parser instance for the specified ITP (auto-registers if needed)."""
    _ensure_registered()
    return _original_get_parser(itp_type)


def get_template_class(itp_type: ITPType) -> Type[ITPTemplate]:
    """Get the template class for the specified ITP (auto-registers if needed)."""
    _ensure_registered()
    return _original_get_template_class(itp_type)


# Re-export base classes for convenience
__all__ = [
    # Enums
    "ITPType",
    # Base classes
    "ITPBenchmarkData",
    "ITPBenchmarkDataSection",
    "ITPCompiler",
    "ITPParser",
    "ITPTemplate",
    # Registry functions
    "register_itp",
    "get_compiler",
    "get_parser",
    "get_template_class",
    "is_registered",
    "get_registered_itps",
]
