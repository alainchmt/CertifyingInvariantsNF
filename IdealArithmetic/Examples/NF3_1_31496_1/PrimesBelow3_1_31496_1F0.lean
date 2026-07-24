
import IdealArithmetic.Examples.NF3_1_31496_1.RI3_1_31496_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![143968534800, -13818137087, -37041908568]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![143968534800, -13818137087, -37041908568]] 
 ![![2, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![143968534800, -13818137087, -37041908568], ![-1236201119831, 477345711912, -78496319829], ![-752333792415, -171972034761, 463527574825]]]
  hmulB := by decide  
  f := ![![![207763728353439112239531, 12775259960406379767023, 18766469124193290860139]], ![![316034370529392489075805, 19432753117849747249140, 28546124502706215080604]], ![![389739530020197985716201, 23964836655147644372464, 35203617660149582562721]]]
  g := ![![![90505221684, -13818137087, -37041908568], ![-578852400001, 477345711912, -78496319829], ![-607930683620, -171972034761, 463527574825]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 1, 0]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-3, 1, 0]] 
 ![![2, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![-3, 1, 0], ![1, -3, 3], ![33, -9, -2]]]
  hmulB := by decide  
  f := ![![![33, 2, 3]], ![![67, 4, 6]], ![![45, 3, 4]]]
  g := ![![![-2, 1, 0], ![2, -3, 3], ![21, -9, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![143968534800, -13818137087, -37041908568]] ![![143968534800, -13818137087, -37041908568]]
  ![![65676815104639605224017, -2215233047302675275696, -21418142439922836368877]] where
 M := ![![![65676815104639605224017, -2215233047302675275696, -21418142439922836368877]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![65676815104639605224017, -2215233047302675275696, -21418142439922836368877]] ![![-3, 1, 0]]
  ![![2, 0, 0]] where
 M := ![![![-906044378878675091120688, 265085796205853158370998, 36190585737937646910666]]]
 hmul := by decide  
 g := ![![![![-453022189439337545560344, 132542898102926579185499, 18095292868968823455333]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N0, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N0
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-51, 24, -8]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-51, 24, -8]] 
 ![![3, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![-51, 24, -8], ![-240, 21, 64], ![728, -280, 45]]]
  hmulB := by decide  
  f := ![![![-18865, -1160, -1704]], ![![-25419, -1563, -2296]], ![![-17304, -1064, -1563]]]
  g := ![![![-25, 24, -8], ![-87, 21, 64], ![336, -280, 45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3673635862846753625, 225889540583815842, 331824878866068914]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3673635862846753625, 225889540583815842, 331824878866068914]] 
 ![![3, 0, 0], ![2, 1, 0], ![1, 0, 1]] where
  M :=![![![3673635862846753625, 225889540583815842, 331824878866068914], ![11176110543164090004, 687211953052133399, 1009493500617516440], ![10108953870194474098, 621593165674208734, 913101493635949241]]]
  hmulB := by decide  
  f := ![![![-1711786801, 461018954, 112383794]], ![![248703518, -600401013, 573402748]], ![![4800303011, -929693760, -716612733]]]
  g := ![![![963343967604351009, 225889540583815842, 331824878866068914], ![2930731045480768922, 687211953052133399, 1009493500617516440], ![2650888681736702463, 621593165674208734, 913101493635949241]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1

def I3N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3107077, -2576682, 1719566]] i)))

def SI3N2: IdealEqSpanCertificate' Table ![![3107077, -2576682, 1719566]] 
 ![![3, 0, 0], ![2, 1, 0], ![2, 0, 1]] where
  M :=![![![3107077, -2576682, 1719566], ![54168996, -12369017, -6010480], ![-71273978, 36946666, -14945699]]]
  hmulB := by decide  
  f := ![![![406930802067563, 25021917076238, 36756436713982]], ![![683948644257590, 42055568598067, 61778353790220]], ![![644545453787612, 39632691392730, 58219220715309]]]
  g := ![![![1607103, -2576682, 1719566], ![30309330, -12369017, -6010480], ![-38425304, 36946666, -14945699]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N2 : Nat.card (O ⧸ I3N2) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N2)

lemma isPrimeI3N2 : Ideal.IsPrime I3N2 := prime_ideal_of_norm_prime hp3.out _ NI3N2
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-51, 24, -8]] ![![3673635862846753625, 225889540583815842, 331824878866068914]]
  ![![-406930802067563, -25021917076238, -36756436713982]] where
 M := ![![![-406930802067563, -25021917076238, -36756436713982]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-406930802067563, -25021917076238, -36756436713982]] ![![3107077, -2576682, 1719566]]
  ![![3, 0, 0]] where
 M := ![![![-3, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1, I3N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)
instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0]] 
 ![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [3, 3, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 4, 2], [1, 0, 3], [0, 1]]
 g := ![![[2, 0, 1], []], ![[0, 3], [1, 4]], ![[2, 3, 2, 3], [0, 4]]]
 h' := ![![[4, 4, 2], [0, 0, 1], [0, 1]], ![[1, 0, 3], [3, 2], [4, 4, 2]], ![[0, 1], [1, 3, 4], [1, 0, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 3], []]
 b := ![[], [3, 2, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [3, 3, 0, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1490, 1235, -2595]
  a := ![-1, -1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![298, 247, -519]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 125 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def PBC5 : ContainsPrimesAboveP 5 ![I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![5, 0, 0]]) timesTableT_eq_Table B_one_repr 5 (by decide) 𝕀

instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-469188367285, -28850095298, -42379914328]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-469188367285, -28850095298, -42379914328]] 
 ![![7, 0, 0], ![0, 1, 0], ![5, 0, 1]] where
  M :=![![![-469188367285, -28850095298, -42379914328], ![-1427387268122, -87769138333, -128930200222], ![-1291092459458, -79388456942, -116619233631]]]
  hmulB := by decide  
  f := ![![![964001, -297938, -20932]], ![![-141242, 164627, -130678]], ![![-739915, 146328, 107113]]]
  g := ![![![-36755542235, -28850095298, -42379914328], ![-111819466716, -87769138333, -128930200222], ![-101142327329, -79388456942, -116619233631]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5431631403, 333987572, 490617606]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![5431631403, 333987572, 490617606]] 
 ![![7, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![5431631403, 333987572, 490617606], ![16524368570, 1016072949, 1492580322], ![14946530724, 919052700, 1350060521]]]
  hmulB := by decide  
  f := ![![![-22971, -8812, 18090]], ![![80741, -27799, 1392]], ![![-20868, 32004, -27799]]]
  g := ![![![728234833, 333987572, 490617606], ![2215470803, 1016072949, 1492580322], ![2003925432, 919052700, 1350060521]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1

def I7N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27760146049, 6023869810, 3428369902]] i)))

def SI7N2: IdealEqSpanCertificate' Table ![![-27760146049, 6023869810, 3428369902]] 
 ![![7, 0, 0], ![5, 1, 0], ![6, 0, 1]] where
  M :=![![![-27760146049, 6023869810, 3428369902], ![119160076576, -58615475167, 21499979332], ![226214662946, -26787869074, -52591605357]]]
  hmulB := by decide  
  f := ![![![-3658620569235219648187, -224966259697448361422, -330468607267629990554]], ![![-4203361877957905184377, -258462057473398791473, -379672917528303575370]], ![![-4574194120509736248640, -281264297006956405738, -413168715304254005421]]]
  g := ![![![-11207102073, 6023869810, 3428369902], ![40462510917, -58615475167, 21499979332], ![96529091494, -26787869074, -52591605357]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N2 : Nat.card (O ⧸ I7N2) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N2)

lemma isPrimeI7N2 : Ideal.IsPrime I7N2 := prime_ideal_of_norm_prime hp7.out _ NI7N2
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-469188367285, -28850095298, -42379914328]] ![![5431631403, 333987572, 490617606]]
  ![![-3658620569235219648187, -224966259697448361422, -330468607267629990554]] where
 M := ![![![-3658620569235219648187, -224966259697448361422, -330468607267629990554]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![-3658620569235219648187, -224966259697448361422, -330468607267629990554]] ![![-27760146049, 6023869810, 3428369902]]
  ![![7, 0, 0]] where
 M := ![![![7, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1, I7N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
    exact isPrimeI7N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1688, 157, -787]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![1688, 157, -787]] 
 ![![11, 0, 0], ![0, 11, 0], ![1, 5, 1]] where
  M :=![![![1688, 157, -787], ![-25814, 8771, -316], ![-1115, -7709, 8928]]]
  hmulB := by decide  
  f := ![![![-6897404, -424117, -623015]], ![![-20983612, -1290269, -1895366]], ![![-11890495, -731139, -1074021]]]
  g := ![![![225, 372, -787], ![-2318, 941, -316], ![-913, -4759, 8928]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [10, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 10], [0, 1]]
 g := ![![[6, 9], [8, 3], [1]], ![[5, 2], [4, 8], [1]]]
 h' := ![![[6, 10], [8, 8], [1, 6], [0, 1]], ![[0, 1], [1, 3], [4, 5], [6, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [4, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [10, 5, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-504, 626, -394]
  a := ![2, -2, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10, 236, -394]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6897404, 424117, 623015]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![6897404, 424117, 623015]] 
 ![![11, 0, 0], ![6, 1, 0], ![3, 0, 1]] where
  M :=![![![6897404, 424117, 623015], ![20983612, 1290269, 1895366], ![18979981, 1167067, 1714386]]]
  hmulB := by decide  
  f := ![![![-1688, -157, 787]], ![![1426, -883, 458]], ![![-359, 658, -597]]]
  g := ![![![225787, 424117, 623015], ![686900, 1290269, 1895366], ![621311, 1167067, 1714386]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![1688, 157, -787]] ![![6897404, 424117, 623015]]
  ![![11, 0, 0]] where
 M := ![![![-11, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0]] 
 ![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [1, 12, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 9], [9, 3], [0, 1]]
 g := ![![[3, 4, 4], [7, 10], [1]], ![[1, 2, 12], [3, 12], [1]], ![[12, 7, 10], [6, 4], [1]]]
 h' := ![![[10, 9], [7, 8, 2], [12, 1, 6], [0, 1]], ![[9, 3], [1, 3, 6], [11, 10, 5], [10, 9]], ![[0, 1], [7, 2, 5], [0, 2, 2], [9, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3], []]
 b := ![[], [5, 8, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [1, 12, 7, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-470952105, 302055962, -189740044]
  a := ![-65, 1, -131]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-36227085, 23235074, -14595388]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def PBC13 : ContainsPrimesAboveP 13 ![I13N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![13, 0, 0]]) timesTableT_eq_Table B_one_repr 13 (by decide) 𝕀

instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6517746, 107213, 2250045]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-6517746, 107213, 2250045]] 
 ![![17, 0, 0], ![0, 17, 0], ![2, 13, 1]] where
  M :=![![![-6517746, 107213, 2250045], ![74358698, -26768151, 2571684], ![21538389, 17035443, -26660938]]]
  hmulB := by decide  
  f := ![![![39403190469978, 2422877205337, 3559133074911]], ![![119874268677400, 7370992795779, 10827764690922]], ![![102682346242445, 6313872382768, 9274886890172]]]
  g := ![![![-648108, -1714316, 2250045], ![4071490, -3541179, 2571684], ![4403545, 21389861, -26660938]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [3, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 16], [0, 1]]
 g := ![![[15, 9], [15], [2], [1]], ![[1, 8], [15], [2], [1]]]
 h' := ![![[6, 16], [15, 14], [3, 10], [14, 6], [0, 1]], ![[0, 1], [14, 3], [12, 7], [16, 11], [6, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [13, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [3, 11, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-84, 525, -501]
  a := ![-2, 1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![54, 414, -501]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-39403190469978, -2422877205337, -3559133074911]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-39403190469978, -2422877205337, -3559133074911]] 
 ![![17, 0, 0], ![11, 1, 0], ![11, 0, 1]] where
  M :=![![![-39403190469978, -2422877205337, -3559133074911], ![-119874268677400, -7370992795779, -10827764690922], ![-108428012375409, -6667169751255, -9793870001116]]]
  hmulB := by decide  
  f := ![![![6517746, -107213, -2250045]], ![![-156676, 1505224, -1607187]], ![![2950401, -1071458, 112379]]]
  g := ![![![1552877800750, -2422877205337, -3559133074911], ![4724239039783, -7370992795779, -10827764690922], ![4273142641216, -6667169751255, -9793870001116]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-6517746, 107213, 2250045]] ![![-39403190469978, -2422877205337, -3559133074911]]
  ![![17, 0, 0]] where
 M := ![![![-17, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0]] 
 ![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [17, 10, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 7], [17, 11], [0, 1]]
 g := ![![[7, 7, 17], [7, 4, 1], [12, 1], []], ![[17, 18, 16], [12, 15, 11], [7, 7], []], ![[4, 13, 5], [3, 0, 7], [10, 11], []]]
 h' := ![![[14, 7], [14, 1, 6], [5, 15, 1], [0, 0, 1], [0, 1]], ![[17, 11], [7, 5, 9], [12, 16, 11], [6, 6, 11], [14, 7]], ![[0, 1], [17, 13, 4], [17, 7, 7], [4, 13, 7], [17, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4], []]
 b := ![[], [2, 18, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [17, 10, 7, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3401, 1368, -3078]
  a := ![-1, -1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![179, 72, -162]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def PBC19 : ContainsPrimesAboveP 19 ![I19N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![19, 0, 0]]) timesTableT_eq_Table B_one_repr 19 (by decide) 𝕀

instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-753546263, 268000448, -22450202]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-753546263, 268000448, -22450202]] 
 ![![23, 0, 0], ![0, 23, 0], ![0, 13, 1]] where
  M :=![![![-753546263, 268000448, -22450202], ![-472856218, -551494445, 781551142], ![8664413168, -2591605648, -283493997]]]
  hmulB := by decide  
  f := ![![![94861639928017247, 5832982108837024, 8568473673860162]], ![![288592613346222370, 17745376863275789, 26067420000371234]], ![![174466964021017126, 10727863027562319, 15758905172910385]]]
  g := ![![![-32762881, 24341438, -22450202], ![-20558966, -465724317, 781551142], ![376713616, 47557231, -283493997]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [17, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 22], [0, 1]]
 g := ![![[2, 13], [13, 16], [9, 6], [1]], ![[20, 10], [21, 7], [12, 17], [1]]]
 h' := ![![[12, 22], [9, 17], [8, 19], [6, 12], [0, 1]], ![[0, 1], [6, 6], [6, 4], [12, 11], [12, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [5, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [17, 11, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-782, 491, -263]
  a := ![-2, 3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-34, 170, -263]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![94861639928017247, 5832982108837024, 8568473673860162]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![94861639928017247, 5832982108837024, 8568473673860162]] 
 ![![23, 0, 0], ![6, 1, 0], ![19, 0, 1]] where
  M :=![![![94861639928017247, 5832982108837024, 8568473673860162], ![288592613346222370, 17745376863275789, 26067420000371234], ![261036198982503088, 16050950411348080, 23578358972112813]]]
  hmulB := by decide  
  f := ![![![-753546263, 268000448, -22450202]], ![![-217136252, 45935141, 28123910]], ![![-245781123, 108713168, -30871645]]]
  g := ![![![-4475532718623825, 5832982108837024, 8568473673860162], ![-13615679471325470, 17745376863275789, 26067420000371234], ![-12315579302422993, 16050950411348080, 23578358972112813]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-753546263, 268000448, -22450202]] ![![94861639928017247, 5832982108837024, 8568473673860162]]
  ![![23, 0, 0]] where
 M := ![![![23, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0)
instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11419258666, -702162977, -1031456101]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-11419258666, -702162977, -1031456101]] 
 ![![29, 0, 0], ![0, 29, 0], ![24, 23, 1]] where
  M :=![![![-11419258666, -702162977, -1031456101], ![-34740214310, -2136153757, -3137945032], ![-31423027049, -1932182015, -2838316734]]]
  hmulB := by decide  
  f := ![![![-36902, 4607, 8317]], ![![279068, -111755, 22138]], ![![198327, -83956, 20746]]]
  g := ![![![459851302, 793838874, -1031456101], ![1398981602, 2415054551, -3137945032], ![1265399123, 2184451823, -2838316734]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [26, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 28], [0, 1]]
 g := ![![[21, 5], [24], [4, 1], [5, 1]], ![[17, 24], [24], [9, 28], [10, 28]]]
 h' := ![![[5, 28], [13, 11], [12, 16], [15, 28], [0, 1]], ![[0, 1], [10, 18], [5, 13], [10, 1], [5, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [26, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [26, 24, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![763, 208, -141]
  a := ![2, 1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![143, 119, -141]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![36902, -4607, -8317]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![36902, -4607, -8317]] 
 ![![29, 0, 0], ![17, 1, 0], ![20, 0, 1]] where
  M :=![![![36902, -4607, -8317], ![-279068, 111755, -22138], ![-218567, -25073, 107148]]]
  hmulB := by decide  
  f := ![![![11419258666, 702162977, 1031456101]], ![![7891986608, 485273254, 712851681]], ![![8958903461, 550877295, 809222026]]]
  g := ![![![9709, -4607, -8317], ![-59867, 111755, -22138], ![-66734, -25073, 107148]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-11419258666, -702162977, -1031456101]] ![![36902, -4607, -8317]]
  ![![29, 0, 0]] where
 M := ![![![-29, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0)

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-82592957, 32018228, -5383624]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-82592957, 32018228, -5383624]] 
 ![![31, 0, 0], ![19, 1, 0], ![4, 0, 1]] where
  M :=![![![-82592957, 32018228, -5383624], ![-145641364, -34140341, 90671060], ![1013532532, -331233044, -2122113]]]
  hmulB := by decide  
  f := ![![![30105700867967173, 1851180463147220, 2719327912905896]], ![![21406365099368325, 1316263821019719, 1933551601534180]], ![![6556980066418520, 403184547984228, 592265863438223]]]
  g := ![![![-21593703, 32018228, -5383624], ![4527125, -34140341, 90671060], ![235982220, -331233044, -2122113]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N0 : Nat.card (O ⧸ I31N0) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N0)

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := prime_ideal_of_norm_prime hp31.out _ NI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![290628888, -113352139, 19702467]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![290628888, -113352139, 19702467]] 
 ![![31, 0, 0], ![23, 1, 0], ![10, 0, 1]] where
  M :=![![![290628888, -113352139, 19702467], ![536829272, 113306685, -320353950], ![-3583000851, 1177788987, -45454]]]
  hmulB := by decide  
  f := ![![![377304204009888660, 23200196341204823, 34080384247507155]], ![![316962889314076778, 19489847149355974, 28629993902057619]], ![![155202954623829129, 9543331300685873, 14018864019309698]]]
  g := ![![![87119465, -113352139, 19702467], ![36590807, 113306685, -320353950], ![-989409452, 1177788987, -45454]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-82592957, 32018228, -5383624]] ![![-82592957, 32018228, -5383624]]
  ![![-3298059916835111, -1954359185284488, 3359200756095360]] where
 M := ![![![-3298059916835111, -1954359185284488, 3359200756095360]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI31N1 : IdealMulLeCertificate' Table 
  ![![-3298059916835111, -1954359185284488, 3359200756095360]] ![![290628888, -113352139, 19702467]]
  ![![31, 0, 0]] where
 M := ![![![-14043687872619463912370664, 4108829841190723954750469, 560954078938033527115323]]]
 hmul := by decide  
 g := ![![![![-453022189439337545560344, 132542898102926579185499, 18095292868968823455333]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N0, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N0
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0 ⊙ MulI31N1)


lemma PB51I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB51I0 : PrimesBelowBoundCertificateInterval O 1 31 51 where
  m := 11
  g := ![3, 3, 1, 3, 2, 1, 2, 1, 2, 2, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB51I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N1]
    · exact ![I3N0, I3N1, I3N2]
    · exact ![I5N0]
    · exact ![I7N0, I7N1, I7N2]
    · exact ![I11N0, I11N1]
    · exact ![I13N0]
    · exact ![I17N0, I17N1]
    · exact ![I19N0]
    · exact ![I23N0, I23N1]
    · exact ![I29N0, I29N1]
    · exact ![I31N0, I31N0, I31N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC2
    · exact PBC3
    · exact PBC5
    · exact PBC7
    · exact PBC11
    · exact PBC13
    · exact PBC17
    · exact PBC19
    · exact PBC23
    · exact PBC29
    · exact PBC31
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2, 2]
    · exact ![3, 3, 3]
    · exact ![125]
    · exact ![7, 7, 7]
    · exact ![121, 11]
    · exact ![2197]
    · exact ![289, 17]
    · exact ![6859]
    · exact ![529, 23]
    · exact ![841, 29]
    · exact ![31, 31, 31]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N0
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
      exact NI3N2
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
      exact NI7N2
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I2N1, I3N0, I3N1, I3N2, I7N0, I7N1, I7N2, I11N1, I17N1, I23N1, I29N1, I31N0, I31N1]
  Il := ![[I2N0, I2N0, I2N1], [I3N0, I3N1, I3N2], [], [I7N0, I7N1, I7N2], [I11N1], [], [I17N1], [], [I23N1], [I29N1], [I31N0, I31N0, I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
