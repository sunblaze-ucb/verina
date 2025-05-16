# Coverage Report

Total executable lines: 8
Covered lines: 8
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def LongestCommonPrefix(str1, str2):
2: ✓     prefix = []
3: ✓     min_length = min(len(str1), len(str2))
4: ✓     for i in range(min_length):
5: ✓         if str1[i] == str2[i]:
6: ✓             prefix.append(str1[i])
7: ✓         else:
8: ✓             break
9: ✓     return prefix
```

## Complete Test File

```python
def LongestCommonPrefix(str1, str2):
    prefix = []
    min_length = min(len(str1), len(str2))
    for i in range(min_length):
        if str1[i] == str2[i]:
            prefix.append(str1[i])
        else:
            break
    return prefix

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = LongestCommonPrefix(['a', 'b', 'c'], ['a', 'b', 'd'])
        assert result == ['a', 'b'], f"Test 1 failed: got {result}, expected {['a', 'b']}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = LongestCommonPrefix(['x', 'y', 'z'], ['x', 'y', 'z'])
        assert result == ['x', 'y', 'z'], f"Test 2 failed: got {result}, expected {['x', 'y', 'z']}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = LongestCommonPrefix(['w', 'o'], ['w', 'o', 'w'])
        assert result == ['w', 'o'], f"Test 3 failed: got {result}, expected {['w', 'o']}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = LongestCommonPrefix(['a', 'x'], ['b', 'y'])
        assert result == [], f"Test 4 failed: got {result}, expected {[]}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = LongestCommonPrefix([], ['h', 'e', 'l', 'l', 'o'])
        assert result == [], f"Test 5 failed: got {result}, expected {[]}"
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
