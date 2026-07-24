import IdealArithmetic.Examples.NF3_1_851175_3.PrimesBelow3_1_851175_3F4
import IdealArithmetic.Examples.NF3_1_851175_3.ClassGroupData3_1_851175_3

set_option linter.all false

noncomputable section


noncomputable def E199RS1 : RelationCertificate Table 7 ![![199, 0, 0], ![98, 1, 0]]
  ![-7, 7, -6] ![![7, 0, 0], ![1, 1, 0]] where
    su := ![![1393, 0, 0], ![686, 7, 0]]
    hsu := by decide
    w := ![![-49, 49, -42], ![-686, 217, 21]]
    hw := by decide
    g := ![![![-274, 2662, 4038], ![344, -9353, 0]], ![![-119, 1311, 1989], ![173, -4606, 0]]]
    h := ![![![-6356, 619245, 18765], ![205, -1244747, 0]], ![![-87381, 8624877, 261360], ![529, -17336879, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N1 : Ideal.span {7} * I199N1 =  Ideal.span {B.equivFun.symm ![-7, 7, -6]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E199RS1 


noncomputable def E211RS1 : RelationCertificate Table 7 ![![211, 0, 0], ![22, 1, 0]]
  ![42, 0, 1] ![![7, 0, 0], ![1, 1, 0]] where
    su := ![![1477, 0, 0], ![154, 7, 0]]
    hsu := by decide
    w := ![![294, 0, 7], ![154, 7, 0]]
    hw := by decide
    g := ![![![63, -119, -181], ![-4, 422, 0]], ![![6, -12, -18], ![1, 42, 0]]]
    h := ![![![-13132, 301721, 39355], ![133, -2767968, 0]], ![![-6887, 157894, 20595], ![212, -1448515, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N1 : Ideal.span {7} * I211N1 =  Ideal.span {B.equivFun.symm ![42, 0, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E211RS1 


noncomputable def E239RS1 : RelationCertificate Table 49 ![![239, 0, 0], ![-11, 1, 0]]
  ![-91, 0, -4] ![![49, 0, 0], ![1, 1, 0]] where
    su := ![![11711, 0, 0], ![-539, 49, 0]]
    hsu := by decide
    w := ![![-4459, 0, -196], ![-539, 49, 0]]
    hw := by decide
    g := ![![![360219245, -719988970, -1080208216], ![-7342206, 17643400860, 0]], ![![-16870450, 33719846, 50590296], ![343883, -826308168, 0]]]
    h := ![![![673649, 6737758, -2021324], ![-2722, 161032144, 0]], ![![81483, 814941, -244482], ![-238, 19477066, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R239N1 : Ideal.span {49} * I239N1 =  Ideal.span {B.equivFun.symm ![-91, 0, -4]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E239RS1 


noncomputable def E241RS1 : RelationCertificate Table 49 ![![241, 0, 0], ![8, 1, 0]]
  ![4732, -3626, 2651] ![![49, 0, 0], ![1, 1, 0]] where
    su := ![![11809, 0, 0], ![392, 49, 0]]
    hsu := by decide
    w := ![![231868, -177674, 129899], ![305270, -95305, -10878]]
    hw := by decide
    g := ![![![373588759, -755998875, -1134118799], ![-7804248, 18521953328, 0]], ![![12345436, -25097331, -37648583], ![-260202, 614836599, 0]]]
    h := ![![![-49012912, 441054834, 147018575], ![203152, -11810491308, 0]], ![![-64390472, 579433611, 193144908], ![266954, -15515974350, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R241N1 : Ideal.span {49} * I241N1 =  Ideal.span {B.equivFun.symm ![4732, -3626, 2651]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E241RS1 


noncomputable def E251RS1 : RelationCertificate Table 7 ![![251, 0, 0], ![69, 1, 0]]
  ![476, -112, -65] ![![7, 0, 0], ![1, 1, 0]] where
    su := ![![1757, 0, 0], ![483, 7, 0]]
    hsu := by decide
    w := ![![3332, -784, -455], ![-6692, 2527, -336]]
    hw := by decide
    g := ![![![-151178, -3132, -5411], ![-22043, 3012, 0]], ![![-43340, -888, -1535], ![-6312, 826, 0]]]
    h := ![![![36838, -2579798, -110563], ![66, 9250416, 0]], ![![-74203, 5184764, 222204], ![477, -18591084, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R251N1 : Ideal.span {7} * I251N1 =  Ideal.span {B.equivFun.symm ![476, -112, -65]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E251RS1 


noncomputable def E251RS2 : RelationCertificate Table 49 ![![251, 0, 0], ![125, 1, 0]]
  ![-63, 0, 1] ![![49, 0, 0], ![1, 1, 0]] where
    su := ![![12299, 0, 0], ![6125, 49, 0]]
    hsu := by decide
    w := ![![-3087, 0, 49], ![49, -98, 0]]
    hw := by decide
    g := ![![![4515033415, -9024432438, -13539465857], ![-92028533, 221144608997, 0]], ![![2244929765, -4487058042, -6731987809], ![-45757703, 109955800880, 0]]]
    h := ![![![-764705, 96197924, 2290427], ![2468, -191632392, 0]], ![![12217, -1539216, -36648], ![-2, 3066216, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R251N2 : Ideal.span {49} * I251N2 =  Ideal.span {B.equivFun.symm ![-63, 0, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E251RS2 
