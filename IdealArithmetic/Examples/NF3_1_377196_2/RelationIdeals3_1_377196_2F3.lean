import IdealArithmetic.Examples.NF3_1_377196_2.PrimesBelow3_1_377196_2F3
import IdealArithmetic.Examples.NF3_1_377196_2.ClassGroupData3_1_377196_2

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 3 ![![139, 0, 0], ![22, 1, 0]]
  ![616525153, 93589262, 60763240] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![417, 0, 0], ![66, 3, 0]]
    hsu := by decide
    w := ![![1849575459, 280767786, 182289720], ![7263651582, 1102631073, 715888074]]
    hw := by decide
    g := ![![![-98731, -5493, 422902], ![-1831, -176250, 0]], ![![-5494, -1286, 68704], ![-427, -28750, 0]]]
    h := ![![![29504038586, 682274298975, 217109424995], ![9578152227, -4311164187295, 0]], ![![115868241859, 2679427198818, 852631997607], ![37615313179, -16930801291145, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {3} * I139N1 =  Ideal.span {B.equivFun.symm ![616525153, 93589262, 60763240]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E139RS1 


noncomputable def E149RS1 : RelationCertificate Table 3 ![![149, 0, 0], ![24, 1, 0]]
  ![16021, 2432, 1579] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![447, 0, 0], ![72, 3, 0]]
    hsu := by decide
    w := ![![48063, 7296, 4737], ![188754, 28653, 18603]]
    hw := by decide
    g := ![![![469, 64, 51], ![22, -50, 0]], ![![25, 9, 18], ![6, -11, 0]]]
    h := ![![![-781893, -19765710, -5765499], ![-258538, 122722990, 0]], ![![-3070643, -77624301, -22642386], ![-1015480, 481960245, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {3} * I149N1 =  Ideal.span {B.equivFun.symm ![16021, 2432, 1579]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E149RS1 


noncomputable def E163RS1 : RelationCertificate Table 3 ![![163, 0, 0], ![-3, 1, 0]]
  ![-144790076104, -21979308227, -14270162541] ![![3, 0, 0], ![-5, 0, 1]] where
    su := ![![489, 0, 0], ![-9, 3, 0]]
    hsu := by decide
    w := ![![-434370228312, -65937924681, -42810487623], ![-2126470916004, -322800850419, -209579871954]]
    hw := by decide
    g := ![![![1055949, 270293, 205233], ![-1691497, 0, 0]], ![![-91784, 1199, -31488], ![142487, 0, 0]]]
    h := ![![![22417325470821, -67295288659624, 157033754188942], ![-825443343838, -3656645171851441, 0]], ![![109744608449663, -329445861598036, 768762887851173], ![-4040979674398, -17901202939956931, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N1 : Ideal.span {3} * I163N1 =  Ideal.span {B.equivFun.symm ![-144790076104, -21979308227, -14270162541]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E163RS1 
