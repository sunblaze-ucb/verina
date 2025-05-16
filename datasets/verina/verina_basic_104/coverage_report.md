# Coverage Report

Total executable lines: 5
Covered lines: 5
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def update_map(m1, m2):
2: ✓     result = {k: v for k, v in m1}
3: ✓     for k, v in m2:
4: ✓         result[k] = v
5: ✓     return list(result.items())
```

## Complete Test File

```python
def update_map(m1, m2):
    result = {k: v for k, v in m1}
    for k, v in m2:
        result[k] = v
    return list(result.items())

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = update_map([(1, 10), (2, 20)], [(2, 30), (3, 40)])
        assert result == '#[(1, 10), (2, 30), (3, 40)]', f"Test 1 failed: got {result}, expected {'#[(1, 10), (2, 30), (3, 40)]'}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = update_map([(1, 100)], [(1, 200)])
        assert result == '#[(1, 200)]', f"Test 2 failed: got {result}, expected {'#[(1, 200)]'}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = update_map([(5, 50), (6, 60)], [])
        assert result == '#[(5, 50), (6, 60)]', f"Test 3 failed: got {result}, expected {'#[(5, 50), (6, 60)]'}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = update_map([], [(7, 70)])
        assert result == '#[(7, 70)]', f"Test 4 failed: got {result}, expected {'#[(7, 70)]'}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = update_map([(1, 1), (2, 2), (3, 3)], [(2, 20), (4, 40)])
        assert result == '#[(1, 1), (2, 20), (3, 3), (4, 40)]', f"Test 5 failed: got {result}, expected {'#[(1, 1), (2, 20), (3, 3), (4, 40)]'}"
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