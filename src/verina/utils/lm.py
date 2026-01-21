import os
import re
from typing import Optional

import dspy
from pydantic import BaseModel


class LMConfig(BaseModel):
    """
    Configuration for the language model.
    """

    provider: str
    model_name: str
    api_base: Optional[str] = None
    api_key: Optional[str] = None
    max_tokens: Optional[int] = None
    temperature: Optional[float] = None

    def get_model(self) -> dspy.LM:
        """
        Get a language model instance based on the configuration.

        Returns:
            dspy.LM: Configured language model instance
        """
        return LMFactory.get_model(
            self.provider,
            self.model_name,
            api_base=self.api_base,
            api_key=self.api_key,
            max_tokens=self.max_tokens,
            temperature=self.temperature,
        )


class LMFactory:
    @staticmethod
    def get_model(
        provider: str,
        model_name: str,
        api_base: Optional[str] = None,
        api_key: Optional[str] = None,
        max_tokens: Optional[int] = None,
        temperature: Optional[float] = None,
        **kwargs,
    ) -> dspy.LM:
        """
        Get a language model instance.

        Args:
            provider: Provider of the language model ('openai', 'local')
            model_name: Name of the model
            api_base: Base URL of the API (required for VLLM models)
            max_tokens: Maximum number of tokens to generate
            temperature: Temperature for sampling
            **kwargs: Additional keyword arguments

        Returns:
            dspy.LM: Configured language model instance
        """
        if provider == "openai":
            return get_openai_model(model_name, max_tokens, temperature)
        elif provider == "local":
            if api_base is None:
                raise ValueError("api_base must be provided for local models")
            return get_local_model(model_name, api_base, api_key, max_tokens, temperature)
        elif provider == "together":
            return get_together_model(model_name, api_key, max_tokens, temperature)
        elif provider == "anthropic":
            return get_anthropic_model(model_name, max_tokens, temperature)
        elif provider == "vertex_ai":
            return get_vertex_model(model_name, max_tokens, temperature)
        else:
            raise ValueError(
                f"Unsupported provider or model: provider: {provider}, model: {model_name}"
            )


def get_openai_model(
    model_name: str, max_tokens: Optional[int], temperature: Optional[float]
) -> dspy.LM:
    """
    Get an OpenAI language model instance.

    Args:
        model_name: Name of the model
        max_tokens: Maximum number of tokens to generate
        temperature: Temperature for sampling

    Returns:
        dspy.LM: Configured language model instance
    """
    if temperature is None:
        temperature = 1.0
    if max_tokens is None:
        max_tokens = 10000
        # DSPy requries openai reasoning model to have at least 16,000 max tokens
        model_pattern = re.match(r"^(?:o[1345]|gpt-5)(?:-(?:mini|nano))?", model_name)
        if model_pattern:
            max_tokens = 16000

    return dspy.LM(
        f"openai/{model_name}",
        cache=False,
        temperature=temperature,
        max_tokens=max_tokens,
    )


def get_local_model(
    model_name: str,
    api_base: str,
    api_key: Optional[str],
    max_tokens: Optional[int],
    temperature: Optional[float],
) -> dspy.LM:
    """
    Get a local model instance.

    Args:
        model_name: Name of the model
        api_base: Base URL of the API
        api_key: API key for authentication
        max_tokens: Maximum number of tokens to generate
        temperature: Temperature for sampling

    Returns:
        dspy.LM: Configured language model instance
    """
    if temperature is None:
        temperature = 1.0
    if max_tokens is None:
        max_tokens = 10000
    return dspy.LM(
        f"hosted_vllm/{model_name}",
        api_base=api_base,
        api_key=api_key,
        temperature=temperature,
        max_tokens=max_tokens,
        cache=False,
    )


def get_together_model(
    model_name: str,
    api_key: Optional[str],
    max_tokens: Optional[int],
    temperature: Optional[float],
) -> dspy.LM:
    """
    Get a Together AI language model instance.

    Args:
        model_name: Name of the model
        api_key: Together AI API key
        max_tokens: Maximum number of tokens to generate
        temperature: Temperature for sampling

    Returns:
        dspy.LM: Configured language model instance
    """
    if temperature is None:
        temperature = 1.0
    if max_tokens is None:
        max_tokens = 10000

    return dspy.LM(
        f"together_ai/{model_name}",
        api_key=api_key or os.getenv("TOGETHER_API_KEY"),
        cache=False,
        temperature=temperature,
        max_tokens=max_tokens,
    )


def get_anthropic_model(
    model_name: str, max_tokens: Optional[int], temperature: Optional[float]
) -> dspy.LM:
    """
    Get an Anthropic language model instance.

    Args:
        model_name: Name of the model
        max_tokens: Maximum number of tokens to generate
        temperature: Temperature for sampling

    Returns:
        dspy.LM: Configured language model instance
    """
    if temperature is None:
        temperature = 1.0
    if max_tokens is None:
        max_tokens = 10000

    return dspy.LM(
        f"anthropic/{model_name}",
        cache=False,
        temperature=temperature,
        max_tokens=max_tokens,
    )


def get_vertex_model(
    model_name: str, max_tokens: Optional[int], temperature: Optional[float]
) -> dspy.LM:
    """
    Get a Vertex AI language model instance.

    Args:
        model_name: Name of the model
        max_tokens: Maximum number of tokens to generate
        temperature: Temperature for sampling

    Returns:
        dspy.LM: Configured language model instance
    """
    if temperature is None:
        temperature = 1.0
    if max_tokens is None:
        max_tokens = 10000

    return dspy.LM(
        f"vertex_ai/{model_name}",
        cache=False,
        temperature=temperature,
        max_tokens=max_tokens,
    )
