import os
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
        )


class LMFactory:
    @staticmethod
    def get_model(
        provider: str,
        model_name: str,
        api_base: Optional[str] = None,
        api_key: Optional[str] = None,
        max_tokens: Optional[int] = None,
        **kwargs,
    ) -> dspy.LM:
        """
        Get a language model instance.

        Args:
            provider: Provider of the language model ('openai', 'local')
            model_name: Name of the model
            api_base: Base URL of the API (required for VLLM models)
            **kwargs: Additional keyword arguments

        Returns:
            dspy.LM: Configured language model instance
        """
        if provider == "openai":
            return get_openai_model(model_name, max_tokens)
        elif provider == "local":
            if api_base is None:
                raise ValueError("api_base must be provided for local models")
            return get_local_model(model_name, api_base, api_key, max_tokens)
        elif provider == "together":
            return get_together_model(model_name, api_key)
        elif provider == "anthropic":
            return get_anthropic_model(model_name, max_tokens)
        elif provider == "vertex_ai":
            return get_vertex_model(model_name, max_tokens)
        else:
            raise ValueError(
                f"Unsupported provider or model: provider: {provider}, model: {model_name}"
            )


def get_openai_model(model_name: str, max_tokens: Optional[int]) -> dspy.LM:
    """
    Get an OpenAI language model instance.

    Args:
        model_name: Name of the model ('gpt-4o-mini', 'gpt-4o', 'o3-mini', 'o1-mini', 'o1-preview')

    Returns:
        dspy.LM: Configured language model instance
    """
    if max_tokens is None:
        max_tokens = 10000
        use_default_max_tokens = True
    else:
        use_default_max_tokens = False
    if model_name == "o4-mini":
        max_tokens = 20000
    model_configs = {
        "gpt-4o-mini": {"temperature": 1.0, "max_tokens": None},
        "gpt-4o": {"temperature": 1.0, "max_tokens": None},
        "o3-mini": {"temperature": 1.0, "max_tokens": max_tokens},
        "o1-mini": {"temperature": 1.0, "max_tokens": max_tokens},
        "o1": {"temperature": 1.0, "max_tokens": max_tokens},
        "o1-preview": {"temperature": 1.0, "max_tokens": max_tokens},
        "o4-mini": {"temperature": 1.0, "max_tokens": max_tokens},
        "gpt-4.1": {"temperature": 1.0, "max_tokens": None},
        "gpt-4.1-nano": {"temperature": 1.0, "max_tokens": None},
    }

    if model_name not in model_configs:
        raise ValueError(f"Unsupported model: {model_name}")

    config = model_configs[model_name]
    kwargs = {k: v for k, v in config.items() if v is not None}

    lm = dspy.LM(f"openai/{model_name}", cache=False, **kwargs)
    if use_default_max_tokens:
        if model_name == "o4-mini":
            lm.kwargs["max_completion_tokens"] = (
                10000  # ensure o4-mini uses the default max tokens
            )
    return lm


def get_local_model(
    model_name: str, api_base: str, api_key: Optional[str], max_tokens: Optional[int]
) -> dspy.LM:
    """
    Get a local model instance.

    Args:
        model_name: Name of the model
        api_base: Base URL of the API

    Returns:
        dspy.LM: Configured language model instance
    """
    if max_tokens is None:
        max_tokens = 10000
    return dspy.LM(
        f"hosted_vllm/{model_name}",
        api_base=api_base,
        api_key=api_key,
        temperature=1.0,
        max_tokens=max_tokens,
        cache=False,
    )


def get_together_model(model_name: str, api_key: Optional[str]) -> dspy.LM:
    """
    Get a Together AI language model instance.

    Args:
        model_name: Name of the model
        api_key: Together AI API key

    Returns:
        dspy.LM: Configured language model instance
    """
    model_configs = {
        "deepseek-ai/DeepSeek-R1": {"temperature": 1.0, "max_tokens": 5000},
    }

    if model_name not in model_configs:
        raise ValueError(f"Unsupported model: {model_name}")

    config = model_configs[model_name]
    kwargs = {k: v for k, v in config.items() if v is not None}

    return dspy.LM(
        f"together_ai/{model_name}",
        api_key=api_key or os.getenv("TOGETHER_API_KEY"),
        cache=False,
        **kwargs,
    )


def get_anthropic_model(model_name: str, max_tokens: Optional[int]) -> dspy.LM:
    """
    Get an Anthropic language model instance.
    Args:
        model_name: Name of the model
    Returns:
        dspy.LM: Configured language model instance
    """
    if max_tokens is None:
        max_tokens = 10000
    model_configs = {
        "claude-3-7-sonnet-20250219": {"temperature": 1.0, "max_tokens": max_tokens},
    }

    if model_name not in model_configs:
        raise ValueError(f"Unsupported model: {model_name}")

    config = model_configs[model_name]
    kwargs = {k: v for k, v in config.items() if v is not None}

    return dspy.LM(f"anthropic/{model_name}", cache=False, **kwargs)


def get_vertex_model(model_name: str, max_tokens: Optional[int]) -> dspy.LM:
    """
    Get a Vertex AI language model instance.

    Args:
        model_name: Name of the model

    Returns:
        dspy.LM: Configured language model instance
    """
    if max_tokens is None:
        max_tokens = 10000
    model_configs = {
        "gemini-2.5-flash-preview-04-17": {
            "temperature": 1.0,
            "max_tokens": max_tokens,
        },
        "gemini-2.5-pro-preview-05-06": {"temperature": 1.0, "max_tokens": max_tokens},
    }

    if model_name not in model_configs:
        raise ValueError(f"Unsupported model: {model_name}")

    config = model_configs[model_name]
    kwargs = {k: v for k, v in config.items() if v is not None}

    return dspy.LM(
        f"vertex_ai/{model_name}",
        cache=False,
        **kwargs,
    )
