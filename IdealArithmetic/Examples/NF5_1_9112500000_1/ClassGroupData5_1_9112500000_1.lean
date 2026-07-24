import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF5_1_9112500000_1.RI5_1_9112500000_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![1406123710432299679, 1293217567636407315, -107900673190397506, -1466975040994369355, -369063443588957237]

def zeta2 := B.equivFun.symm ![-18159125272979288138568386159, -9555167402444725407843057862, 80609822611219060237323456, 6815874491657594203676545830, 1644846264641709260369986720]

lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![15841956483708313751501258479, 7895000629087074131528185069, 7735608709070812841378553194, 13953957684339845913268284625, -1968610731342282805006348593])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![225003325290819273951038957012597197957561, 327657734275130421375259949602765036471682, 218676420611774289632426215798028150823344, 353885765828283259939214309550079463788170, 36429263439450230441792757273227645498720])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

