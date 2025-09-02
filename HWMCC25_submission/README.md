# rIC3-multi - HWMCC25 Submission

This directory contains the rIC3-multi model checker submission for HWMCC25 (Hardware Model Checking Competition 2025).

## Usage

The tool follows the HWMCC25 standard format:

```bash
./rIC3-multi <benchmark> <certificate.sat> <certificate.unsat>
```

### Arguments

- `<benchmark>`: Path to the input model file (AIG or BTOR2 format)
- `<certificate.sat>`: Output path for SAT certificate (counterexample/witness)
- `<certificate.unsat>`: Output path for UNSAT certificate (invariant/proof)

### Output

The tool outputs one of the following results to stdout:
- `sat` - Property is violated (counterexample found)
- `unsat` - Property holds (invariant found) 
- `unknown` - Result could not be determined

### Certificates

- When result is `sat`: A counterexample witness is written to `<certificate.sat>`
- When result is `unsat`: An invariant proof is written to `<certificate.unsat>`
- When result is `unknown`: No certificate files are generated

## Example

```bash
./rIC3-multi benchmark.aig witness.sat proof.unsat
```

## About rIC3-multi

rIC3-multi is an enhanced version of the rIC3 model checker with multi-timeframe optimization capabilities. It extends IC3/PDR (Property Directed Reachability) algorithm with multi-timeframe reasoning.
We also use ABC (A System for Sequential Synthesis and Verification) for circuit simplification preprocessing to improve verification performance.

### Key Features

- IC3/PDR algorithm with multi-timeframe blocking
- Dynamic timeframe expansion strategy
- ABC circuit simplification for preprocessing optimization

## Files

- `rIC3-multi`: Wrapper script implementing HWMCC25 interface
- `rIC3`: Main rIC3 binary executable
- `abc`: ABC executable

## License

Please refer to the main repository for license information.
