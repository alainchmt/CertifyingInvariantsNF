
import IdealArithmetic.Examples.NF3_1_643700_1.RI3_1_643700_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![14, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![14, 1, 0]] 
 ![![37, 0, 0], ![14, 1, 0], ![28, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![14, 1, 0], ![3, 12, 6], ![-183, 19, 17]]]
  hmulB := by decide  
  f := ![![![-689, -3255, -1632], ![-333, 10064, 0]], ![![-264, -1221, -612], ![-110, 3774, 0]], ![![-518, -2463, -1235], ![-261, 7616, 0]]]
  g := ![![![1, 0, 0], ![-14, 37, 0], ![-28, 0, 37]], ![![0, 1, 0], ![-9, 12, 6], ![-25, 19, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![348757991623795585, -70136999716599996, 25093335811738236]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![348757991623795585, -70136999716599996, 25093335811738236]] 
 ![![37, 0, 0], ![27, 1, 0], ![36, 0, 1]] where
  M :=![![![348757991623795585, -70136999716599996, 25093335811738236], ![-4802491452697897176, 965805371480022061, -345541990864385268], ![9246723927059231520, -1859563046661902880, 665307044520498553]]]
  hmulB := by decide  
  f := ![![![8839805893, -216713892, -445965468]], ![![8638818867, -136523927, -396736416]], ![![11396343684, -69026736, -465685607]]]
  g := ![![![36191807966200513, -70136999716599996, 25093335811738236], ![-498370940852449275, 965805371480022061, -345541990864385268], ![959564123897098956, -1859563046661902880, 665307044520498553]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-5, 1, 0]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-5, 1, 0]] 
 ![![37, 0, 0], ![32, 1, 0], ![7, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-5, 1, 0], ![3, -7, 6], ![-183, 19, -2]]]
  hmulB := by decide  
  f := ![![![67, -154, 132], ![0, -814, 0]], ![![58, -133, 114], ![1, -703, 0]], ![![17, -30, 25], ![32, -154, 0]]]
  g := ![![![1, 0, 0], ![-32, 37, 0], ![-7, 0, 37]], ![![-1, 1, 0], ![5, -7, 6], ![-21, 19, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![14, 1, 0]] ![![348757991623795585, -70136999716599996, 25093335811738236]]
  ![![37, 0, 0], ![-29, -12, 1]] where
 M := ![![![12904045690080436645, -2595068989514199852, 928453425034314732]], ![![80120430035241014, -16112624552377883, 5764710499950036]]]
 hmul := by decide  
 g := ![![![![234885342657470798, -117256716530251632, 29019978879542539], ![-145285793508759211, 0, 0]]], ![![![1458388718908393, -728039777489771, 180183273004829], ![-902070601228637, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-29, -12, 1]] ![![37, 0, 0], ![-5, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-185, 37, 0]], ![![-1073, -444, 37], ![-74, 74, -74]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-5, 1, 0]]], ![![![-29, -12, 1]], ![![-2, 2, -2]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![0, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![0, 1, 0]] 
 ![![41, 0, 0], ![0, 1, 0], ![21, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![0, 1, 0], ![3, -2, 6], ![-183, 19, 3]]]
  hmulB := by decide  
  f := ![![![-41, 27, -84], ![41, 574, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-21, 14, -43], ![14, 294, 0]]]
  g := ![![![1, 0, 0], ![0, 41, 0], ![-21, 0, 41]], ![![0, 1, 0], ![-3, -2, 6], ![-6, 19, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![22571136431, 1310928764, -170453886]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![22571136431, 1310928764, -170453886]] 
 ![![41, 0, 0], ![40, 1, 0], ![0, 0, 1]] where
  M :=![![![22571136431, 1310928764, -170453886], ![35125847430, 16710655069, 7354210926], ![-215525058114, 28487178122, 22924391117]]]
  hmulB := by decide  
  f := ![![![-173580876027314061101, 34907993924530471480, -12489242733533123598]], ![![-111048283880058766126, 22332372711407670897, -7989987170603450874]], ![![-112248809202288770886, 22573804438299379358, -8076365650193127859]]]
  g := ![![![-728439369, 1310928764, -170453886], ![-15446350130, 16710655069, 7354210926], ![-33049077634, 28487178122, 22924391117]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![0, 1, 0]] ![![41, 0, 0], ![0, 1, 0]]
  ![![173580876027314061101, -34907993924530471480, 12489242733533123598]] where
 M := ![![![1681, 0, 0], ![0, 41, 0]], ![![0, 41, 0], ![3, -2, 6]]]
 hmul := by decide  
 g := ![![![![-925416593671, -53748079324, 6988609326]], ![![-35125847430, -16710655069, -7354210926]]], ![![![-35125847430, -16710655069, -7354210926]], ![![31602161811, -3449623046, -2983574712]]]]
 hle2 := by decide  
def MulI41N1 : IdealMulLeCertificate' Table 
  ![![173580876027314061101, -34907993924530471480, 12489242733533123598]] ![![22571136431, 1310928764, -170453886]]
  ![![41, 0, 0]] where
 M := ![![![-41, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [9, 15, 25, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 17, 38], [11, 25, 5], [0, 1]]
 g := ![![[4, 18, 14], [35, 21, 35], [33, 36], [8, 18, 1], []], ![[31, 19, 32, 9], [25, 31, 25, 38], [4, 40], [33, 29, 42, 14], [22, 25]], ![[14, 17, 23, 37], [31, 19, 30, 32], [5, 6], [28, 10, 7, 26], [12, 25]]]
 h' := ![![[7, 17, 38], [29, 27, 10], [28, 14, 32], [14, 19, 37], [0, 0, 1], [0, 1]], ![[11, 25, 5], [18, 41, 29], [2, 27, 42], [9, 32, 13], [23, 27, 25], [7, 17, 38]], ![[0, 1], [26, 18, 4], [39, 2, 12], [16, 35, 36], [13, 16, 17], [11, 25, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30], []]
 b := ![[], [23, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [9, 15, 25, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4284864, 1122687, -303408]
  a := ![-5, 3, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-99648, 26109, -7056]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def PBC43 : ContainsPrimesAboveP 43 ![I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![43, 0, 0]]) timesTableT_eq_Table B_one_repr 43 (by decide) 𝕀

instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [1, 3, 43, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 2, 46], [2, 44, 1], [0, 1]]
 g := ![![[45, 36, 12], [28, 46, 3], [1, 4, 17], [13, 4, 1], []], ![[23, 31, 22, 19], [9, 44, 17, 41], [17, 30, 39, 23], [22, 32, 24, 38], [0, 1]], ![[4, 45, 17, 27], [24, 43, 28, 4], [6, 46, 28, 3], [31, 10, 23, 4], [45, 1]]]
 h' := ![![[2, 2, 46], [19, 12, 23], [46, 21, 12], [34, 4, 39], [0, 0, 1], [0, 1]], ![[2, 44, 1], [41, 44, 13], [42, 32, 37], [10, 46, 20], [4, 7, 44], [2, 2, 46]], ![[0, 1], [40, 38, 11], [19, 41, 45], [41, 44, 35], [6, 40, 2], [2, 44, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 40], []]
 b := ![[], [41, 34, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [1, 3, 43, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1984622, -550605, 183253]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![42226, -11715, 3899]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def PBC47 : ContainsPrimesAboveP 47 ![I47N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![47, 0, 0]]) timesTableT_eq_Table B_one_repr 47 (by decide) 𝕀

instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [25, 47, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 33, 14], [10, 19, 39], [0, 1]]
 g := ![![[29, 52, 6], [6, 36], [28, 36, 1], [26, 40], [1]], ![[51, 11, 40, 50], [49, 36], [15, 17, 48, 8], [14, 37], [51, 12, 0, 41]], ![[37, 34, 33, 2], [], [25, 33, 10, 14], [0, 38], [21, 36, 48, 12]]]
 h' := ![![[17, 33, 14], [24, 6, 35], [42, 52, 6], [28, 22, 52], [28, 6, 27], [0, 1]], ![[10, 19, 39], [31, 14, 7], [39, 46, 47], [11, 15, 24], [34, 50, 14], [17, 33, 14]], ![[0, 1], [38, 33, 11], [12, 8], [4, 16, 30], [51, 50, 12], [10, 19, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 20], []]
 b := ![[], [41, 26, 44], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [25, 47, 26, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-33622278648, 9220852921, -2754536034]
  a := ![-129, 65, -194]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-634382616, 173978357, -51972378]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def PBC53 : ContainsPrimesAboveP 53 ![I53N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![53, 0, 0]]) timesTableT_eq_Table B_one_repr 53 (by decide) 𝕀

instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19521367390788108445125, -3784060657546156024322, -1229050003984344643616]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-19521367390788108445125, -3784060657546156024322, -1229050003984344643616]] 
 ![![59, 0, 0], ![6, 1, 0], ![26, 0, 1]] where
  M :=![![![-19521367390788108445125, -3784060657546156024322, -1229050003984344643616], ![213563968756496601708762, -35305196151398344625185, -26391513957229970076780], ![868237250900707836488014, -46087102409705726946182, -56683599447097814034027]]]
  hmulB := by decide  
  f := ![![![-784917190553047399887813685492301128683316035, 157850825195592156906053642900800354345730582, -56475238188089990168329924803776111964374200]], ![![103373185096423055460943306014230894583352104, -20788871446515060770540130256963488790228873, 7437759448826153049514449731708764718559588]], ![![-698620150919927601979996495367903562375074624, 140496053148331133123853260193479903335758210, -50266117115364414696290834280803005558842571]]]
  g := ![![![595564350136979464997, -3784060657546156024322, -1229050003984344643616], ![18840245907675693075528, -35305196151398344625185, -26391513957229970076780], ![44381922898025175644912, -46087102409705726946182, -56683599447097814034027]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![19, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![19, 1, 0]] 
 ![![59, 0, 0], ![19, 1, 0], ![45, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![19, 1, 0], ![3, 17, 6], ![-183, 19, 22]]]
  hmulB := by decide  
  f := ![![![1621, 10460, 3696], ![708, -36344, 0]], ![![518, 3362, 1188], ![237, -11682, 0]], ![![1237, 7978, 2819], ![538, -27720, 0]]]
  g := ![![![1, 0, 0], ![-19, 59, 0], ![-45, 0, 59]], ![![0, 1, 0], ![-10, 17, 6], ![-26, 19, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-26, 1, 0]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-26, 1, 0]] 
 ![![59, 0, 0], ![33, 1, 0], ![7, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-26, 1, 0], ![3, -28, 6], ![-183, 19, -23]]]
  hmulB := by decide  
  f := ![![![4313, -51362, 11016], ![-2714, -108324, 0]], ![![2403, -28702, 6156], ![-1533, -60534, 0]], ![![517, -6094, 1307], ![-310, -12852, 0]]]
  g := ![![![1, 0, 0], ![-33, 59, 0], ![-7, 0, 59]], ![![-1, 1, 0], ![15, -28, 6], ![-11, 19, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-19521367390788108445125, -3784060657546156024322, -1229050003984344643616]] ![![59, 0, 0], ![19, 1, 0]]
  ![![59, 0, 0], ![-10, -6, 1]] where
 M := ![![![-1151760676056498398262375, -223259578795223205434998, -72513950235076333973344], ![-157342011668477458748613, -107202348644775309087303, -49743464032932518305484]]]
 hmul := by decide  
 g := ![![![![-18922448131945726808985, -3424709102240727042638, -1288941929868582807230], ![3533623627170051653226, 0, 0]], ![![-2565301977735365107207, -1756081892466453536157, -853260737815959492336], ![598919498209091742340, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-10, -6, 1]] ![![59, 0, 0], ![-26, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-1534, 59, 0]], ![![-590, -354, 59], ![59, 177, -59]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-26, 1, 0]]], ![![![-10, -6, 1]], ![![1, 3, -1]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1, I59N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
    exact isPrimeI59N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-15, -30, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-15, -30, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![46, 31, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-15, -30, 1], ![-273, 64, -177], ![5347, -591, -84]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-46, -31, 61]], ![![-1, -1, 1], ![129, 91, -177], ![151, 33, -84]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [49, 52, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 60], [0, 1]]
 g := ![![[16, 5], [25], [34, 22], [24, 48], [9, 1]], ![[0, 56], [25], [49, 39], [29, 13], [18, 60]]]
 h' := ![![[9, 60], [51, 35], [42, 5], [44, 12], [47, 32], [0, 1]], ![[0, 1], [0, 26], [26, 56], [30, 49], [30, 29], [9, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43]]
 b := ![[], [10, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [49, 52, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1337, -4077, 1911]
  a := ![-5, 4, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1463, -1038, 1911]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-6, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-6, 1, 0]] 
 ![![61, 0, 0], ![55, 1, 0], ![23, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-6, 1, 0], ![3, -8, 6], ![-183, 19, -3]]]
  hmulB := by decide  
  f := ![![![-1565, 4236, -3180], ![244, 32330, 0]], ![![-1406, 3812, -2862], ![245, 29097, 0]], ![![-589, 1597, -1199], ![103, 12190, 0]]]
  g := ![![![1, 0, 0], ![-55, 61, 0], ![-23, 0, 61]], ![![-1, 1, 0], ![5, -8, 6], ![-19, 19, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-15, -30, 1]] ![![61, 0, 0], ![-6, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-366, 61, 0]], ![![-915, -1830, 61], ![-183, 244, -183]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-6, 1, 0]]], ![![![-15, -30, 1]], ![![-3, 4, -3]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0)
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7931422235806658029712397438, -934452337022245670685080073, -784477433132376497303306660]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![7931422235806658029712397438, -934452337022245670685080073, -784477433132376497303306660]] 
 ![![67, 0, 0], ![37, 1, 0], ![8, 0, 1]] where
  M :=![![![7931422235806658029712397438, -934452337022245670685080073, -784477433132376497303306660], ![140756013252158161994449878561, -5104744319664004077680268956, -7960146321530603516020400418], ![283185050613000796849742505739, -1280568307642761299647081527, -11345960871039985425712282641]]]
  hmulB := by decide  
  f := ![![![-47724718204020224919112460287588776191852964777939114510, 9597682712776003698143483891069297190153434742990842973, -3433820612506207152213279422138212498015292590906623554]], ![![-16546751542116185105338812607705730453601505200281531307, 3327635598589880128714286072824038626883980477604694657, -1190548182441675580592093634912130101189419331019699766]], ![![-24584139320623624676815795179113838927115155756584925551, 4943995016531081343975416909310052038693490783131221715, -1768842803408540615505479281438642493490091726645651771]]]
  g := ![![![728089226428190445126668857, -934452337022245670685080073, -784477433132376497303306660], ![5870339158984643895474373631, -5104744319664004077680268956, -7960146321530603516020400418], ![6288563656180639527498250498, -1280568307642761299647081527, -11345960871039985425712282641]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11845213844354407613369341718, -2382132538888801189545549475, 852269871650321029816534986]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![11845213844354407613369341718, -2382132538888801189545549475, 852269871650321029816534986]] 
 ![![67, 0, 0], ![44, 1, 0], ![61, 0, 1]] where
  M :=![![![11845213844354407613369341718, -2382132538888801189545549475, 852269871650321029816534986], ![-163111784128675152025062550863, 32802606483488109558974605402, -11735985618381844047823691892], ![314055662970654710423071050927, -63158185543543964227512674731, 22596483532344745670879927999]]]
  hmulB := by decide  
  f := ![![![-503496961530454, -122556407388241, -44662035237672]], ![![-214154971358369, -97006637930632, -42305285082090]], ![![-28340612870485, -132337460463704, -67663478704243]]]
  g := ![![![965232587832717569172610216, -2382132538888801189545549475, 852269871650321029816534986], ![-13291512637027753517950746017, 32802606483488109558974605402, -11735985618381844047823691892], ![25591497483784472395670942256, -63158185543543964227512674731, 22596483532344745670879927999]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![709721351316957785232519411, -142728560812099036012484024, 51064854796411072584123100]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![709721351316957785232519411, -142728560812099036012484024, 51064854796411072584123100]] 
 ![![67, 0, 0], ![52, 1, 0], ![25, 0, 1]] where
  M :=![![![709721351316957785232519411, -142728560812099036012484024, 51064854796411072584123100], ![-9773054110179523390931979372, 1965410714072966236355826359, -703176800483360998322534844], ![18817052392727340210754973092, -3784204606154514208503781556, 1353897619605293201461652439]]]
  hmulB := by decide  
  f := ![![![-100676081697663, -30368085409064, -11975147460644]], ![![-46788186853848, -27561315729897, -12549874967012]], ![![70938860810287, -16189815840676, -11084136136037]]]
  g := ![![![102313211099042251392218077, -142728560812099036012484024, 51064854796411072584123100], ![-1408880466117757354080172820, 1965410714072966236355826359, -703176800483360998322534844], ![2712660468994473865916571687, -3784204606154514208503781556, 1353897619605293201461652439]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![7931422235806658029712397438, -934452337022245670685080073, -784477433132376497303306660]] ![![11845213844354407613369341718, -2382132538888801189545549475, 852269871650321029816534986]]
  ![![100676081697663, 30368085409064, 11975147460644]] where
 M := ![![![100676081697663, 30368085409064, 11975147460644]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![100676081697663, 30368085409064, 11975147460644]] ![![709721351316957785232519411, -142728560812099036012484024, 51064854796411072584123100]]
  ![![67, 0, 0]] where
 M := ![![![-67, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1, I67N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
    exact isPrimeI67N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0]] 
 ![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [66, 25, 57, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 4, 56], [8, 66, 15], [0, 1]]
 g := ![![[58, 2, 54], [36, 55, 50], [64, 1, 24], [0, 60], [14, 1], []], ![[26, 19, 28, 65], [15, 3, 60, 66], [4, 34, 59, 55], [6, 50], [52, 25], [48, 12]], ![[59, 14, 14, 60], [25, 21, 58, 1], [11, 43, 58, 15], [16, 40], [14, 16], [18, 12]]]
 h' := ![![[6, 4, 56], [38, 32, 57], [36, 39, 60], [1, 67, 33], [70, 10, 29], [0, 0, 1], [0, 1]], ![[8, 66, 15], [58, 9, 16], [3, 27, 38], [68, 16, 37], [40, 38, 60], [63, 44, 66], [6, 4, 56]], ![[0, 1], [55, 30, 69], [3, 5, 44], [10, 59, 1], [1, 23, 53], [12, 27, 4], [8, 66, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32, 10], []]
 b := ![[], [15, 45, 48], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [66, 25, 57, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4389433, 1017501, -237140]
  a := ![-5, 3, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-61823, 14331, -3340]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def PBC71 : ContainsPrimesAboveP 71 ![I71N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![71, 0, 0]]) timesTableT_eq_Table B_one_repr 71 (by decide) 𝕀

instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2236219147872059756774033395, -174669230330145805267873518, -175061653978372472261091864]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![2236219147872059756774033395, -174669230330145805267873518, -175061653978372472261091864]] 
 ![![73, 0, 0], ![0, 73, 0], ![72, 20, 1]] where
  M :=![![![2236219147872059756774033395, -174669230330145805267873518, -175061653978372472261091864], ![31512274987051725007976190558, -740613817056725605650964985, -1573200343915992248390516700], ![56998285669323945897356990346, 357579357273051617393332302, -1964083276664199576512516303]]]
  hmulB := by decide  
  f := ![![![27632481923106547364587675970361142654734472206508135, -5557032163725895231276727994771477438667223616678834, 1988172787037546501712115161756539200667243081292720]], ![![-380506716519048695507147258585761106038107154726604262, 76521829204271721359671320033278342344746537984427483, -27377674621242731882524022483359247030001612456194844]], ![![-66958458280847024963203065026537323069048971704604546, 13465685324090266912483421023896918859756182272104502, -4817699147923752757815017090928494309578710153523319]]]
  g := ![![![203296688141299695336611611, 45569367797771282739095394, -175061653978372472261091864], ![1983324654095933793042375246, 420868398099494785783005055, -1573200343915992248390516700], ![2717976460125291991866550194, 543003354665164974625255594, -1964083276664199576512516303]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [69, 46, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 72], [0, 1]]
 g := ![![[25, 18], [12], [41], [1, 24], [72], [1]], ![[0, 55], [12], [41], [65, 49], [72], [1]]]
 h' := ![![[27, 72], [36, 23], [34, 31], [4, 48], [12, 43], [4, 27], [0, 1]], ![[0, 1], [0, 50], [68, 42], [59, 25], [5, 30], [3, 46], [27, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63]]
 b := ![[], [31, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [69, 46, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-343407, -226657, 154629]
  a := ![43, -22, 85]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-157215, -45469, 154629]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-107415627163416417512045594139, 5156482188052914200326222188, 6729520695490966834473613916]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-107415627163416417512045594139, 5156482188052914200326222188, 6729520695490966834473613916]] 
 ![![73, 0, 0], ![23, 1, 0], ![66, 0, 1]] where
  M :=![![![-107415627163416417512045594139, 5156482188052914200326222188, 6729520695490966834473613916], ![-1216032840710688188107692680064, 10132301674806123942300625889, 51127455214790385705378174876], ![-1905957699868891555989425450392, -43346773032304933717747670664, 49373754006052628612878964661]]]
  hmulB := by decide  
  f := ![![![2716479967321846763876302829276703976421708491735259746293, -546297889293162379287726619210111761250071537809941458492, 195452278321974111189179439144836063370160907872955077364]], ![![343457241747968850461259559619573377769994993914114666187, -69070992050918562857144477128544627476667624009415950851, 24711943844004830345100078116507768220873347641605250144]], ![![3442609805258195944184072578767141886173463589697450056114, -692326279927126829786705902121932288178485750399686035568, 247697733061015168485914166811604194601034148811678453445]]]
  g := ![![![-9180316210836126783490509903, 5156482188052914200326222188, 6729520695490966834473613916], ![-66075175663114993086788583799, 10132301674806123942300625889, 51127455214790385705378174876], ![-57091091568840432451112886202, -43346773032304933717747670664, 49373754006052628612878964661]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![2236219147872059756774033395, -174669230330145805267873518, -175061653978372472261091864]] ![![-107415627163416417512045594139, 5156482188052914200326222188, 6729520695490966834473613916]]
  ![![73, 0, 0]] where
 M := ![![![305858745451461349458076545976116759360346522037276683935, 17349580651234322615549591826362775923838189303535538454, -2525161255269102315716359387039862474418694772863227052]]]
 hmul := by decide  
 g := ![![![![4189845828102210266548993780494750128223924959414749095, 237665488373072912541775230498120218134769716486788198, -34591250072179483776936429959450170882447873600866124]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![6, 37, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![6, 37, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![6, 37, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![6, 37, 1], ![-72, -49, 225], ![-6914, 682, 138]]]
  hmulB := by decide  
  f := ![![![-5, -37, -1], ![79, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-6, -37, 79]], ![![0, 0, 1], ![-18, -106, 225], ![-98, -56, 138]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [73, 55, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 78], [0, 1]]
 g := ![![[4, 13], [34, 65], [49, 9], [59, 51], [23], [1]], ![[0, 66], [14, 14], [28, 70], [19, 28], [23], [1]]]
 h' := ![![[24, 78], [46, 31], [57, 67], [38, 3], [16, 50], [6, 24], [0, 1]], ![[0, 1], [0, 48], [6, 12], [31, 76], [31, 29], [29, 55], [24, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [19, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [73, 55, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1158, -189, 360]
  a := ![1, 0, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-42, -171, 360]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![12, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![12, 1, 0]] 
 ![![79, 0, 0], ![12, 1, 0], ![20, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![12, 1, 0], ![3, 10, 6], ![-183, 19, 15]]]
  hmulB := by decide  
  f := ![![![6826, 23413, 14058], ![1343, -185097, 0]], ![![1029, 3547, 2130], ![238, -28045, 0]], ![![1724, 5927, 3559], ![367, -46860, 0]]]
  g := ![![![1, 0, 0], ![-12, 79, 0], ![-20, 0, 79]], ![![0, 1, 0], ![-3, 10, 6], ![-9, 19, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![6, 37, 1]] ![![79, 0, 0], ![12, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![948, 79, 0]], ![![474, 2923, 79], ![0, 395, 237]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![12, 1, 0]]], ![![![6, 37, 1]], ![![0, 5, 3]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0)


lemma PB228I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB228I1 : PrimesBelowBoundCertificateInterval O 31 79 228 where
  m := 11
  g := ![3, 3, 1, 1, 1, 3, 2, 3, 1, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB228I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0]
    · exact ![I53N0]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![37, 37, 37]
    · exact ![41, 41, 41]
    · exact ![79507]
    · exact ![103823]
    · exact ![148877]
    · exact ![59, 59, 59]
    · exact ![3721, 61]
    · exact ![67, 67, 67]
    · exact ![357911]
    · exact ![5329, 73]
    · exact ![6241, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
      exact NI37N2
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
      exact NI67N2
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N0, I37N1, I37N2, I41N0, I41N1, I59N0, I59N1, I59N2, I61N1, I67N0, I67N1, I67N2, I73N1, I79N1]
  Il := ![[I37N0, I37N1, I37N2], [I41N0, I41N0, I41N1], [], [], [], [I59N0, I59N1, I59N2], [I61N1], [I67N0, I67N1, I67N2], [], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
