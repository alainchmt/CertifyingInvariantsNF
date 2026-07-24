import IdealArithmetic.Examples.NF3_1_358280_1.PrimesBelow3_1_358280_1F3
import IdealArithmetic.Examples.NF3_1_358280_1.ClassGroupData3_1_358280_1

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 2 ![![139, 0, 0], ![27, 1, 0]]
  ![-5933, 2142, -279] ![![2, 0, 0], ![-20, 2, 1]] where
    su := ![![278, 0, 0], ![54, 2, 0]]
    hsu := by decide
    w := ![![-11866, 4284, -558], ![-66650, 24062, -3134]]
    hw := by decide
    g := ![![![52, 225, 45], ![-99, 0, 0]], ![![27, 49, 9], ![-18, 0, 0]]]
    h := ![![![-201317, -7817, -16], ![1036190, 1945, 0]], ![![-1130701, -43908, -90], ![5819782, 10943, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {2} * I139N1 =  Ideal.span {B.equivFun.symm ![-5933, 2142, -279]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E139RS1 


noncomputable def E149RS1 : RelationCertificate Table 2 ![![149, 0, 0], ![28, 1, 0]]
  ![38831, -14019, 1826] ![![2, 0, 0], ![-20, 2, 1]] where
    su := ![![298, 0, 0], ![56, 2, 0]]
    hsu := by decide
    w := ![![77662, -28038, 3652], ![436202, -157480, 20512]]
    hw := by decide
    g := ![![![-84, -608, -116], ![213, 0, 0]], ![![-17, -130, -24], ![39, 0, 0]]]
    h := ![![![112323, 4041, 17], ![-596332, -707, 0]], ![![630953, 22770, 98], ![-3349782, -4346, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {2} * I149N1 =  Ideal.span {B.equivFun.symm ![38831, -14019, 1826]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E149RS1 


noncomputable def E163RS1 : RelationCertificate Table 2 ![![163, 0, 0], ![-29, 1, 0]]
  ![-25907, -1743, 320] ![![2, 0, 0], ![-20, 2, 1]] where
    su := ![![326, 0, 0], ![-58, 2, 0]]
    hsu := by decide
    w := ![![-51814, -3486, 640], ![629326, -85884, -26976]]
    hw := by decide
    g := ![![![900750, 21276714, -7987155], ![8275781, 0, 0]], ![![-197147, -4657048, 1748228], ![-1811402, 0, 0]]]
    h := ![![![-259296, 9156, -6], ![-1456529, 1298, 0]], ![![3150804, -111477, 8], ![17698841, -14792, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N1 : Ideal.span {2} * I163N1 =  Ideal.span {B.equivFun.symm ![-25907, -1743, 320]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E163RS1 


noncomputable def E167RS1 : RelationCertificate Table 2 ![![167, 0, 0], ![-36, 1, 0]]
  ![20277146, -7320569, 953517] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![334, 0, 0], ![-72, 2, 0]]
    hsu := by decide
    w := ![![40554292, -14641138, 1907034], ![-135399414, 48882656, -6367052]]
    hw := by decide
    g := ![![![33894, -7377, 77232], ![-3687, -158746, 0]], ![![-5486, 1444, -16615], ![724, 34017, 0]]]
    h := ![![![1393874662, -40283059, 48039], ![6465466428, -7068996, 0]], ![![-4653756633, 134493955, -160392], ![-21586379389, 23601938, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N1 : Ideal.span {2} * I167N1 =  Ideal.span {B.equivFun.symm ![20277146, -7320569, 953517]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E167RS1 
