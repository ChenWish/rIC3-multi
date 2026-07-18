use std::time::Duration;

/// A median calculator for Duration values using a sorted vector.
/// Optimized for small n where cache locality matters.
///
/// Complexity:
/// - add: O(n) - binary search + shift
/// - median: O(1) - direct access
/// - remove_smallest/largest: O(n) - single memmove
pub struct MedianCalculator {
    data: Vec<Duration>,
}

impl MedianCalculator {
    pub fn new() -> Self {
        MedianCalculator { data: Vec::new() }
    }

    /// Add a duration value. O(n) complexity.
    /// Uses binary search to find position, then inserts (shifts elements once).
    pub fn add(&mut self, value: Duration) {
        let pos = self.data.partition_point(|&x| x < value);
        self.data.insert(pos, value);
    }

    pub fn reset(&mut self) {
        self.data.clear();
    }

    #[allow(unused)]
    pub fn count(&self) -> usize {
        self.data.len()
    }

    /// Get the median value. O(1) complexity.
    /// For even count, returns the lower median.
    pub fn median(&self) -> Option<Duration> {
        if self.data.is_empty() {
            return None;
        }
        // For len=5: index 2 (middle)
        // For len=4: index 1 (lower median)
        let mid = (self.data.len() - 1) / 2;
        Some(self.data[mid])
    }

    /// Remove the `num` largest elements. O(n) complexity.
    /// If num >= count(), clears all data.
    pub fn remove_largest(&mut self, num: usize) {
        if num >= self.data.len() {
            self.data.clear();
        } else {
            self.data.truncate(self.data.len() - num);
        }
    }

    /// Remove the `num` smallest elements. O(n) complexity.
    /// If num >= count(), clears all data.
    pub fn remove_smallest(&mut self, num: usize) {
        if num >= self.data.len() {
            self.data.clear();
        } else {
            self.data.drain(0..num);
        }
    }
}

impl Default for MedianCalculator {
    fn default() -> Self {
        Self::new()
    }
}

/// A bounded median calculator that automatically removes outliers when full.
/// When count exceeds max_size, removes (removal_ratio * max_size) elements
/// evenly from both ends (largest and smallest).
pub struct BoundedMedianCalculator {
    inner: MedianCalculator,
    max_size: usize,
    remove_per_side: usize,
}

impl BoundedMedianCalculator {
    /// Create a new bounded median calculator.
    ///
    /// # Arguments
    /// * `max_size` - Maximum number of elements before triggering removal
    /// * `removal_ratio` - Fraction of elements to remove (split evenly between largest/smallest)
    ///
    /// # Example
    /// max_size=100, removal_ratio=0.2 -> removes 10 largest + 10 smallest when count > 100
    pub fn new(max_size: usize, removal_ratio: f64) -> Self {
        assert!(max_size > 0, "max_size must be positive");
        assert!(
            (0.0..1.0).contains(&removal_ratio),
            "removal_ratio must be in [0.0, 1.0)"
        );

        let total_remove = (max_size as f64 * removal_ratio) as usize;
        let remove_per_side = total_remove / 2;

        BoundedMedianCalculator {
            inner: MedianCalculator::new(),
            max_size,
            remove_per_side,
        }
    }

    /// Add a duration value.
    /// If count exceeds max_size, removes outliers first.
    pub fn add(&mut self, value: Duration) {
        if self.inner.count() >= self.max_size {
            self.inner.remove_largest(self.remove_per_side);
            self.inner.remove_smallest(self.remove_per_side);
        }
        self.inner.add(value);
    }
    
    #[allow(unused)]
    pub fn reset(&mut self) {
        self.inner.reset();
    }

    #[allow(unused)]
    pub fn count(&self) -> usize {
        self.inner.count()
    }

    pub fn median(&self) -> Option<Duration> {
        self.inner.median()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_median_calculator_odd() {
        let mut calculator = MedianCalculator::new();

        calculator.add(Duration::from_millis(3));
        calculator.add(Duration::from_millis(1));
        calculator.add(Duration::from_millis(5));
        calculator.add(Duration::from_millis(2));
        calculator.add(Duration::from_millis(4));

        // Sorted: [1, 2, 3, 4, 5], median = 3
        assert_eq!(calculator.median(), Some(Duration::from_millis(3)));
    }

    #[test]
    fn test_median_calculator_even() {
        let mut calculator = MedianCalculator::new();

        calculator.add(Duration::from_millis(1));
        calculator.add(Duration::from_millis(2));
        calculator.add(Duration::from_millis(3));
        calculator.add(Duration::from_millis(4));

        // Sorted: [1, 2, 3, 4], lower median = 2
        assert_eq!(calculator.median(), Some(Duration::from_millis(2)));
    }

    #[test]
    fn test_median_single_element() {
        let mut calculator = MedianCalculator::new();
        calculator.add(Duration::from_millis(42));
        assert_eq!(calculator.median(), Some(Duration::from_millis(42)));
    }

    #[test]
    fn test_empty_data() {
        let calculator = MedianCalculator::new();
        assert_eq!(calculator.median(), None);
    }

    #[test]
    fn test_reset() {
        let mut calculator = MedianCalculator::new();
        calculator.add(Duration::from_millis(1));
        calculator.add(Duration::from_millis(2));
        calculator.reset();
        assert_eq!(calculator.median(), None);
        assert_eq!(calculator.count(), 0);
    }

    #[test]
    fn test_remove_largest() {
        let mut calculator = MedianCalculator::new();
        for i in 1..=5 {
            calculator.add(Duration::from_millis(i));
        }
        // [1, 2, 3, 4, 5]
        calculator.remove_largest(2); // Remove 4 and 5
        // [1, 2, 3]
        assert_eq!(calculator.count(), 3);
        assert_eq!(calculator.median(), Some(Duration::from_millis(2)));
    }

    #[test]
    fn test_remove_smallest() {
        let mut calculator = MedianCalculator::new();
        for i in 1..=5 {
            calculator.add(Duration::from_millis(i));
        }
        // [1, 2, 3, 4, 5]
        calculator.remove_smallest(2); // Remove 1 and 2
        // [3, 4, 5]
        assert_eq!(calculator.count(), 3);
        assert_eq!(calculator.median(), Some(Duration::from_millis(4)));
    }

    #[test]
    fn test_remove_all() {
        let mut calculator = MedianCalculator::new();
        calculator.add(Duration::from_millis(1));
        calculator.add(Duration::from_millis(2));
        calculator.remove_largest(5); // More than count, clears all
        assert_eq!(calculator.count(), 0);
        assert_eq!(calculator.median(), None);
    }

    #[test]
    fn test_remove_zero() {
        let mut calculator = MedianCalculator::new();
        calculator.add(Duration::from_millis(1));
        calculator.add(Duration::from_millis(2));
        calculator.remove_largest(0); // No-op
        calculator.remove_smallest(0); // No-op
        assert_eq!(calculator.count(), 2);
    }

    #[test]
    fn test_insertion_order_independence() {
        let mut calc1 = MedianCalculator::new();
        let mut calc2 = MedianCalculator::new();

        // Add in different orders
        calc1.add(Duration::from_millis(5));
        calc1.add(Duration::from_millis(1));
        calc1.add(Duration::from_millis(3));

        calc2.add(Duration::from_millis(1));
        calc2.add(Duration::from_millis(3));
        calc2.add(Duration::from_millis(5));

        assert_eq!(calc1.median(), calc2.median());
    }

    #[test]
    fn test_bounded_calculator_under_limit() {
        // max_size=10, removal_ratio=0.2 -> removes 1+1=2 when full
        let mut calc = BoundedMedianCalculator::new(10, 0.2);

        for i in 1..=5 {
            calc.add(Duration::from_millis(i));
        }

        assert_eq!(calc.count(), 5);
        assert_eq!(calc.median(), Some(Duration::from_millis(3)));
    }

    #[test]
    fn test_bounded_calculator_triggers_removal() {
        // max_size=10, removal_ratio=0.4 -> removes 2+2=4 when count >= 10
        let mut calc = BoundedMedianCalculator::new(10, 0.4);

        // Add 10 elements [1..=10]
        for i in 1..=10 {
            calc.add(Duration::from_millis(i));
        }
        assert_eq!(calc.count(), 10);

        // Add 11th element, should trigger removal first
        // Before: [1,2,3,4,5,6,7,8,9,10] count=10
        // Remove 2 largest (9,10) and 2 smallest (1,2)
        // After removal: [3,4,5,6,7,8] count=6
        // Then add 11: [3,4,5,6,7,8,11] count=7
        calc.add(Duration::from_millis(11));
        assert_eq!(calc.count(), 7);
    }

    #[test]
    fn test_bounded_calculator_preserves_middle() {
        // max_size=100, removal_ratio=0.2 -> removes 10+10=20 when full
        let mut calc = BoundedMedianCalculator::new(100, 0.2);

        // Add 100 elements [1..=100]
        for i in 1..=100 {
            calc.add(Duration::from_millis(i));
        }

        // Median of [1..=100] is 50
        assert_eq!(calc.median(), Some(Duration::from_millis(50)));

        // Add 101st, triggers removal of 10 smallest and 10 largest
        // Removes [1..=10] and [91..=100], keeps [11..=90] (80 elements)
        // Then adds 101: [11..=90, 101] (81 elements)
        calc.add(Duration::from_millis(101));
        assert_eq!(calc.count(), 81);

        // Median of [11..=90, 101] -> sorted: [11,12,...,90,101]
        // 81 elements, median at index (81-1)/2 = 40 -> value is 11+40 = 51
        assert_eq!(calc.median(), Some(Duration::from_millis(51)));
    }

    #[test]
    fn test_bounded_calculator_reset() {
        let mut calc = BoundedMedianCalculator::new(10, 0.2);
        for i in 1..=5 {
            calc.add(Duration::from_millis(i));
        }
        calc.reset();
        assert_eq!(calc.count(), 0);
        assert_eq!(calc.median(), None);
    }
}
