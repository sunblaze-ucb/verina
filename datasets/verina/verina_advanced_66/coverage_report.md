# Coverage Report

Total executable lines: 3
Covered lines: 3
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def reverseWords(words_str):
2: ✓     words = words_str.split()
3: ✓     return " ".join(reversed(words))
```

## Complete Test File

```python
def reverseWords(words_str):
    words = words_str.split()
    return " ".join(reversed(words))

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = reverseWords('the sky is blue')
        assert result == 'blue is sky the', f"Test 1 failed: got {result}, expected {'blue is sky the'}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = reverseWords('  hello world  ')
        assert result == 'world hello', f"Test 2 failed: got {result}, expected {'world hello'}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = reverseWords('a good   example')
        assert result == 'example good a', f"Test 3 failed: got {result}, expected {'example good a'}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = reverseWords('  Bob    Loves  Alice   ')
        assert result == 'Alice Loves Bob', f"Test 4 failed: got {result}, expected {'Alice Loves Bob'}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = reverseWords('this lab is interesting')
        assert result == 'interesting is lab this', f"Test 5 failed: got {result}, expected {'interesting is lab this'}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    return test_results

if __name__ == '__main__':
    results = run_tests()
    print(f"\n{sum(results)}/{len(results)} tests passed")

```
