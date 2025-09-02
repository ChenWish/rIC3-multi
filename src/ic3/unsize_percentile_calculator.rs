pub struct UnsizePercentileCalculator {
    data: Vec<usize>,
}

impl UnsizePercentileCalculator {
    pub fn new() -> Self {
        UnsizePercentileCalculator {
            data: Vec::new(),
        }
    }

    pub fn add(&mut self, value: usize) {
        self.data.push(value);
    }

    pub fn reset(&mut self) {
        self.data.clear();
    }

    pub fn count(&self) -> usize {
        self.data.len()
    }

    pub fn percentile(&mut self, ratio: f64) -> Option<usize> {
        assert!(ratio >= 0.0 && ratio <= 1.0, "Ratio must be between 0 and 1");
        
        if self.data.is_empty() {
            return None;
        }

        self.data.sort_unstable();
        let index = (ratio * (self.data.len() - 1) as f64).round() as usize;
        Some(self.data[index])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_percentile_calculator() {
        let mut calculator = UnsizePercentileCalculator::new();
        
        // Add some test data
        calculator.add(1);
        calculator.add(2);
        calculator.add(3);
        calculator.add(4);
        calculator.add(5);

        // Test different percentiles
        assert_eq!(calculator.percentile(0.75), Some(4));  // 75th percentile
        assert_eq!(calculator.percentile(0.5), Some(3));   // 50th percentile (median)
        assert_eq!(calculator.percentile(0.25), Some(2));  // 25th percentile
    }

    #[test]
    fn test_empty_data() {
        let mut calculator = UnsizePercentileCalculator::new();
        assert_eq!(calculator.percentile(0.75), None);
    }

    #[test]
    #[should_panic(expected = "Ratio must be between 0 and 1")]
    fn test_invalid_ratio() {
        let mut calculator = UnsizePercentileCalculator::new();
        let _ = calculator.percentile(1.5);
    }
}
