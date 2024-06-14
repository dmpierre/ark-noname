use ark_ff::PrimeField;
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystemRef, LinearCombination, SynthesisError, Variable,
};
use noname::backends::r1cs::LinearCombination as NoNameLinearCombination;
use noname::backends::{
    r1cs::{GeneratedWitness, R1CS},
    BackendField,
};
use noname::witness::CompiledCircuit;
use num_bigint::BigUint;

struct NoNameCircuit<BF: BackendField> {
    compiled_circuit: CompiledCircuit<R1CS<BF>>,
    witness: GeneratedWitness<BF>,
}
impl<F: PrimeField, BF: BackendField> ConstraintSynthesizer<F> for NoNameCircuit<BF> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        for var in self.compiled_circuit.circuit.backend.public_inputs.iter() {
            let value: BigUint = self.witness.witness[var.index].into();
            cs.new_input_variable(|| Ok(F::from(value)))?;
        }

        for var in self.compiled_circuit.circuit.backend.public_outputs.iter() {
            let value: BigUint = self.witness.witness[var.index].into();
            cs.new_input_variable(|| Ok(F::from(value)))?;
        }

        for var in self
            .compiled_circuit
            .circuit
            .backend
            .private_input_cell_vars
            .iter()
        {
            let value: BigUint = self.witness.witness[var.index].into();
            cs.new_witness_variable(|| Ok(F::from(value)))?;
        }

        let public_io_length = self.compiled_circuit.circuit.backend.public_inputs.len()
            + self.compiled_circuit.circuit.backend.public_outputs.len();

        let make_index = |index| {
            if index < public_io_length {
                match index == 1 {
                    true => Variable::One,
                    false => Variable::Instance(index),
                }
            } else {
                Variable::Witness(index - public_io_length)
            }
        };

        let make_lc = |lc_data: NoNameLinearCombination<BF>| {
            //lc_data.iter().fold(
            //    LinearCombination::<F>::zero(),
            //    |lc: LinearCombination<F>, (index, coeff)| lc + (*coeff, make_index(*index)),
            //)
            let mut lc = LinearCombination::<F>::zero();
            for (cellvar, coeff) in lc_data.terms.into_iter() {
                let idx = make_index(cellvar.index);
                let coeff = F::from(Into::<BigUint>::into(coeff));
                lc += (coeff, idx)
            }

            // add constant
            let constant = F::from(Into::<BigUint>::into(lc_data.constant));
            lc += (constant, make_index(1));
            lc
        };

        for constraint in self.compiled_circuit.circuit.backend.constraints {
            cs.enforce_constraint(
                make_lc(constraint.a),
                make_lc(constraint.b),
                make_lc(constraint.c),
            )?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::Fr;
    use ark_relations::r1cs::ConstraintSystem;
    use noname::{
        backends::r1cs::R1csBn254Field,
        circuit_writer::CircuitWriter,
        compiler::{typecheck_next_file, Sources},
        inputs::parse_inputs,
        type_checker::TypeChecker,
    };
    const SIMPLE_ADDITION: &str = "fn main(pub public_input: Field, private_input: Field) {
    let xx = private_input + public_input;
    let yy = private_input * public_input;
    assert_eq(xx, yy);
}
";
    pub fn compile_source_code<BF: BackendField>(
        code: &str,
    ) -> Result<CompiledCircuit<R1CS<BF>>, noname::error::Error> {
        let mut sources = Sources::new();

        // parse the transitive dependency
        let mut tast = TypeChecker::<R1CS<BF>>::new();
        let mut node_id = 0;
        node_id = typecheck_next_file(
            &mut tast,
            None,
            &mut sources,
            "main.no".to_string(),
            code.to_string(),
            node_id,
        )
        .unwrap();
        let r1cs = R1CS::<BF>::new();

        // compile
        CircuitWriter::generate_circuit(tast, r1cs)
    }

    #[test]
    fn cs_is_satisfied() {
        let compiled_circuit = compile_source_code::<R1csBn254Field>(SIMPLE_ADDITION).unwrap();
        let inputs_public = r#"{"public_input": "2"}"#;
        let inputs_private = r#"{"private_input": "2"}"#;

        println!("{:?}", compiled_circuit.main_info().sig());
        let json_public = parse_inputs(inputs_public).unwrap();
        let json_private = parse_inputs(inputs_private).unwrap();
        let generated_witness = compiled_circuit
            .generate_witness(json_public, json_private)
            .unwrap();
        let noname_circuit = NoNameCircuit {
            compiled_circuit,
            witness: generated_witness,
        };
        let cs = ConstraintSystem::<Fr>::new_ref();
        noname_circuit.generate_constraints(cs.clone()).unwrap();
        let is_sat = cs.is_satisfied();
        println!("{:?}", is_sat);
        //let json_private =
        //
        // compiled_circuit.
    }
}
