# Coverage Report

Total executable lines: 2
Covered lines: 2
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def replaceWithColon(s):
2: ✓     return ''.join(':' if c in ' ,.' else c for c in s)
```

## Complete Test File

```python
def replaceWithColon(s):
    return ''.join(':' if c in ' ,.' else c for c in s)

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = replaceWithColon('Hello, world. How are you?')
        assert result == 'Hello::world::How:are:you?', f"Test 1 failed: got {result}, expected {'Hello::world::How:are:you?'}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = replaceWithColon('No-changes!')
        assert result == 'No-changes!', f"Test 2 failed: got {result}, expected {'No-changes!'}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = replaceWithColon(',. ')
        assert result == ':::', f"Test 3 failed: got {result}, expected {':::'}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = replaceWithColon('')
        assert result == '', f"Test 4 failed: got {result}, expected {''}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    return test_results

if __name__ == '__main__':
    results = run_tests()
    print(f"\n{sum(results)}/{len(results)} tests passed")

```
