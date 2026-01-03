"""Dataset template module.

This module provides backward-compatible exports for template rendering.
The actual implementations are in the ITP-specific modules (lean/, coq/).

For new code, consider using:
    from verina.lean.template import LeanGenerationTaskTemplate
    from verina.coq.template import CoqGenerationTaskTemplate
"""

# Re-export from Lean template module for backward compatibility
from verina.lean.template import LeanGenerationTaskTemplate

# Re-export ITP base class
from verina.itp.base import ITPTemplate

# Export public API - maintains backward compatibility
__all__ = [
    # Lean-specific (backward compatible)
    "LeanGenerationTaskTemplate",
    # ITP-generic
    "ITPTemplate",
]
