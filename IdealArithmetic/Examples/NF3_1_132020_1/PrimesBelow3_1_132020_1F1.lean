
import IdealArithmetic.Examples.NF3_1_132020_1.RI3_1_132020_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-95892855932511956791, 25145845366245348708, -5224060836726893954]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-95892855932511956791, 25145845366245348708, -5224060836726893954]] 
 ![![37, 0, 0], ![9, 1, 0], ![30, 0, 1]] where
  M :=![![![-95892855932511956791, 25145845366245348708, -5224060836726893954], ![365684258570882576780, -95892855932511956791, 19921784529518454754], ![-1394524917066291832780, 365684258570882576780, -75971071402993502037]]]
  hmulB := by decide  
  f := ![![![-53353471147, -13850530076, 36783782]], ![![-13047462299, -4811033563, -364397088]], ![![-17125456590, -11299750460, -1785505513]]]
  g := ![![![-4472530787213872339, 25145845366245348708, -5224060836726893954], ![17055849353457744467, -95892855932511956791, 19921784529518454754], ![-65041921678768377370, 365684258570882576780, -75971071402993502037]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-749659, 196582, -40840]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-749659, 196582, -40840]] 
 ![![37, 0, 0], ![29, 1, 0], ![10, 0, 1]] where
  M :=![![![-749659, 196582, -40840], ![2858800, -749659, 155742], ![-10901940, 2858800, -593917]]]
  hmulB := by decide  
  f := ![![![5297, 306, -284]], ![![4689, 383, -222]], ![![1390, 620, 67]]]
  g := ![![![-163301, 196582, -40840], ![622743, -749659, 155742], ![-2374810, 2858800, -593917]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15081581664887, -2404355632362, 406576407582]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![-15081581664887, -2404355632362, 406576407582]] 
 ![![37, 0, 0], ![35, 1, 0], ![33, 0, 1]] where
  M :=![![![-15081581664887, -2404355632362, 406576407582], ![-28460348530740, -15081581664887, -1997779224780], ![139844545734600, -28460348530740, -17079360889667]]]
  hmulB := by decide  
  f := ![![![200726283016879578175285429, -52636163816374031792674134, 10935187025279898090303594]], ![![169188021995167361346317255, -44365931096113825258602953, 9217042407937899985358250]], ![![257919884187395011863523161, -67633959397565835553499946, 14050985893514110309538743]]]
  g := ![![![1504157946421, -2404355632362, 406576407582], ![15278965517785, -15081581664887, -1997779224780], ![45934477126203, -28460348530740, -17079360889667]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-95892855932511956791, 25145845366245348708, -5224060836726893954]] ![![-749659, 196582, -40840]]
  ![![200726283016879578175285429, -52636163816374031792674134, 10935187025279898090303594]] where
 M := ![![![200726283016879578175285429, -52636163816374031792674134, 10935187025279898090303594]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![200726283016879578175285429, -52636163816374031792674134, 10935187025279898090303594]] ![![-15081581664887, -2404355632362, 406576407582]]
  ![![37, 0, 0]] where
 M := ![![![37, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1856393116297079904023, 486799290598058952322, -101132774512860712548]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-1856393116297079904023, 486799290598058952322, -101132774512860712548]] 
 ![![41, 0, 0], ![13, 1, 0], ![36, 0, 1]] where
  M :=![![![-1856393116297079904023, 486799290598058952322, -101132774512860712548], ![7079294215900249878360, -1856393116297079904023, 385666516085198239774], ![-26996656125963876784180, 7079294215900249878360, -1470726600211881664249]]]
  hmulB := by decide  
  f := ![![![-296816483087, -38777274898, 10241725376]], ![![-111598416011, -19534659921, 2551387326]], ![![-211900120112, -51534211528, 1057319047]]]
  g := ![![![-110829366136801478841, 486799290598058952322, -101132774512860712548], ![422644149968174438995, -1856393116297079904023, 385666516085198239774], ![-1611739593293643543656, 7079294215900249878360, -1470726600211881664249]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6407991080541, 1680358262903, -349095195053]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-6407991080541, 1680358262903, -349095195053]] 
 ![![41, 0, 0], ![14, 1, 0], ![9, 0, 1]] where
  M :=![![![-6407991080541, 1680358262903, -349095195053], ![24436663653710, -6407991080541, 1331263067850], ![-93188414749500, 24436663653710, -5076728012691]]]
  hmulB := by decide  
  f := ![![![-16922331, -1405343, 795123]], ![![-7135884, -892613, 256622]], ![![-2672819, -1666017, -253084]]]
  g := ![![![-653442683066, 1680358262903, -349095195053], ![2491882223674, -6407991080541, 1331263067850], ![-9502711067981, 24436663653710, -5076728012691]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-1856393116297079904023, 486799290598058952322, -101132774512860712548]] ![![-1856393116297079904023, 486799290598058952322, -101132774512860712548]]
  ![![9622637541058711847250950367583334045027089, -2523330369815915950559384184902791311644092, 524223034504693262986845916090442459132284]] where
 M := ![![![9622637541058711847250950367583334045027089, -2523330369815915950559384184902791311644092, 524223034504693262986845916090442459132284]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI41N1 : IdealMulLeCertificate' Table 
  ![![9622637541058711847250950367583334045027089, -2523330369815915950559384184902791311644092, 524223034504693262986845916090442459132284]] ![![-6407991080541, 1680358262903, -349095195053]]
  ![![41, 0, 0]] where
 M := ![![![-172175064629431217451190598832020151855418834145804014469, 45149218979795625834509058663550448456334187915574966779, -9379770822808279567056173668479648948017953597971249161]]]
 hmul := by decide  
 g := ![![![![-4199391820230029693931478020293174435498020345019610109, 1101200462921844532549001430818303620886199705257926019, -228774898117275111391613991914137779219950087755396321]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-691599, 181357, -37677]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-691599, 181357, -37677]] 
 ![![43, 0, 0], ![0, 43, 0], ![32, 21, 1]] where
  M :=![![![-691599, 181357, -37677], ![2637390, -691599, 143680], ![-10057600, 2637390, -547919]]]
  hmulB := by decide  
  f := ![![![-867, -71, 41]], ![![-2870, -867, -30]], ![![-1998, -543, -5]]]
  g := ![![![11955, 22618, -37677], ![-45590, -86253, 143680], ![173856, 328923, -547919]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [40, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 42], [0, 1]]
 g := ![![[39, 14], [3, 11], [23], [6, 15], [1]], ![[0, 29], [0, 32], [23], [41, 28], [1]]]
 h' := ![![[31, 42], [9, 33], [6, 22], [18, 25], [3, 31], [0, 1]], ![[0, 1], [0, 10], [0, 21], [19, 18], [18, 12], [31, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [33, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [40, 12, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-170, -82, -8]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2, 2, -8]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-867, -71, 41]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-867, -71, 41]] 
 ![![43, 0, 0], ![21, 1, 0], ![32, 0, 1]] where
  M :=![![![-867, -71, 41], ![-2870, -867, -30], ![2100, -2870, -897]]]
  hmulB := by decide  
  f := ![![![-691599, 181357, -37677]], ![![-276423, 72486, -15059]], ![![-748576, 196298, -40781]]]
  g := ![![![-16, -71, 41], ![379, -867, -30], ![2118, -2870, -897]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-691599, 181357, -37677]] ![![-867, -71, 41]]
  ![![43, 0, 0]] where
 M := ![![![43, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0)
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [3, 1, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 4, 23], [27, 42, 24], [0, 1]]
 g := ![![[41, 3, 14], [37, 44, 36], [37, 1, 2], [3, 45, 1], []], ![[8, 32, 14, 19], [9, 1, 25, 35], [25, 8, 30, 44], [31, 46, 6, 11], [19, 12]], ![[2, 45, 42, 16], [22, 44, 24, 9], [10, 8, 2, 28], [16, 10, 18, 8], [18, 12]]]
 h' := ![![[18, 4, 23], [30, 26, 25], [30, 41, 6], [38, 3, 40], [0, 0, 1], [0, 1]], ![[27, 42, 24], [29, 26, 3], [20, 40, 20], [9, 0, 10], [32, 42, 42], [18, 4, 23]], ![[0, 1], [29, 42, 19], [17, 13, 21], [0, 44, 44], [17, 5, 4], [27, 42, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 27], []]
 b := ![[], [33, 21, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [3, 1, 2, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![132023, 0, 0]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2809, 0, 0]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3469444947, 1519580536, 637049690]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-3469444947, 1519580536, 637049690]] 
 ![![53, 0, 0], ![0, 53, 0], ![50, 40, 1]] where
  M :=![![![-3469444947, 1519580536, 637049690], ![-44593478300, -3469444947, 2156630226], ![-150964115820, -44593478300, -1312814721]]]
  hmulB := by decide  
  f := ![![![-1900497765742938879, 498364789238318048, -103535512127118822]], ![![7247485848898317540, -1900497765742938879, 394829277111199226]], ![![3155405590018902110, -827437458847232740, 171900509235099779]]]
  g := ![![![-666451499, -452120888, 637049690], ![-2875943200, -1693106679, 2156630226], ![-1609875090, 149417180, -1312814721]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [40, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 52], [0, 1]]
 g := ![![[47, 4], [4], [45, 7], [4], [28, 1]], ![[0, 49], [4], [29, 46], [4], [3, 52]]]
 h' := ![![[28, 52], [3, 51], [2, 51], [48, 31], [46, 2], [0, 1]], ![[0, 1], [0, 2], [52, 2], [15, 22], [49, 51], [28, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [33, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [40, 25, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2606, -173, 103]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-48, -81, 103]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1900497765742938879, -498364789238318048, 103535512127118822]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![1900497765742938879, -498364789238318048, 103535512127118822]] 
 ![![53, 0, 0], ![12, 1, 0], ![15, 0, 1]] where
  M :=![![![1900497765742938879, -498364789238318048, 103535512127118822], ![-7247485848898317540, 1900497765742938879, -394829277111199226], ![27638049397783945820, -7247485848898317540, 1505668488631739653]]]
  hmulB := by decide  
  f := ![![![3469444947, -1519580536, -637049690]], ![![1626921088, -278594745, -184928802]], ![![3830297925, 411316420, -155526993]]]
  g := ![![![119393255748980625, -498364789238318048, 103535512127118822], ![-455302261908407466, 1900497765742938879, -394829277111199226], ![1736280231228069085, -7247485848898317540, 1505668488631739653]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-3469444947, 1519580536, 637049690]] ![![1900497765742938879, -498364789238318048, 103535512127118822]]
  ![![53, 0, 0]] where
 M := ![![![-53, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2650563, 379883, 281879]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-2650563, 379883, 281879]] 
 ![![59, 0, 0], ![23, 1, 0], ![2, 0, 1]] where
  M :=![![![-2650563, 379883, 281879], ![-19731530, -2650563, 661762], ![-46323340, -19731530, -1988801]]]
  hmulB := by decide  
  f := ![![![-18329019100823, 4806392254587, -998530181723]], ![![-5960514010141, 1563016995842, -324717493335]], ![![-5139125140714, 1347625376776, -279969786295]]]
  g := ![![![-202570, 379883, 281879], ![676405, -2650563, 661762], ![6974228, -19731530, -1988801]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![704867893, 96032491, -23286945]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![704867893, 96032491, -23286945]] 
 ![![59, 0, 0], ![39, 1, 0], ![13, 0, 1]] where
  M :=![![![704867893, 96032491, -23286945], ![1630086150, 704867893, 72745546], ![-5092188220, 1630086150, 777613439]]]
  hmulB := by decide  
  f := ![![![-429533239307626127, 112635882102558299, -23400155848091971]], ![![-256165854637813237, 67174002757494026, -13955429691883399]], ![![-200515812691725129, 52580972486435523, -10923721001328058]]]
  g := ![![![-46401169, 96032491, -23286945], ![-454329725, 704867893, 72745546], ![-1335161403, 1630086150, 777613439]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12886418587209, -3711129725885, -87044870777]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![-12886418587209, -3711129725885, -87044870777]] 
 ![![59, 0, 0], ![55, 1, 0], ![43, 0, 1]] where
  M :=![![![-12886418587209, -3711129725885, -87044870777], ![6093140954390, -12886418587209, -3798174596662], ![265872221766340, 6093140954390, -16684593183871]]]
  hmulB := by decide  
  f := ![![![238147464911500794973952219, -62449066395962847634061865, 12973822009071680185904477]], ![![206609203889788578144984045, -54178833675702641099990684, 11255677391729682080959133]], ![![232264544038591795004253603, -60906396536634238326745315, 12653331642621896195248938]]]
  g := ![![![3304553318303, -3711129725885, -87044870777], ![14884197811989, -12886418587209, -3798174596662], ![10986219935277, 6093140954390, -16684593183871]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-2650563, 379883, 281879]] ![![704867893, 96032491, -23286945]]
  ![![-2684435663418689, 472714216229936, 308551209623034]] where
 M := ![![![-2684435663418689, 472714216229936, 308551209623034]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![-2684435663418689, 472714216229936, 308551209623034]] ![![-12886418587209, -3711129725885, -87044870777]]
  ![![59, 0, 0]] where
 M := ![![![119508271611046066334185443601, 5750741737156218162030995401, -6709836181085705750757206893]]]
 hmul := by decide  
 g := ![![![![2025563925610950276850600739, 97470198934851155288660939, -113726036967554334758596727]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [15, 19, 60, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [54, 27, 43], [8, 33, 18], [0, 1]]
 g := ![![[33, 50, 41], [37, 47], [18, 9, 3], [31, 24, 1], [1]], ![[49, 20, 16, 18], [19, 41], [56, 17, 40, 50], [2, 25, 22, 6], [50, 16, 38, 24]], ![[6, 3, 15, 30], [0, 15], [38, 15, 38, 38], [27, 20, 8, 31], [28, 26, 27, 37]]]
 h' := ![![[54, 27, 43], [60, 36, 23], [35, 52, 48], [23, 8, 8], [46, 42, 1], [0, 1]], ![[8, 33, 18], [15, 11, 50], [42, 27, 38], [39, 17, 59], [5, 34, 9], [54, 27, 43]], ![[0, 1], [22, 14, 49], [12, 43, 36], [24, 36, 55], [31, 46, 51], [8, 33, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 49], []]
 b := ![[], [2, 28, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [15, 19, 60, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-144875, -38918, 1708]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2375, -638, 28]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def PBC61 : ContainsPrimesAboveP 61 ![I61N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![61, 0, 0]]) timesTableT_eq_Table B_one_repr 61 (by decide) 𝕀

instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [3, 15, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 58, 54], [28, 8, 13], [0, 1]]
 g := ![![[10, 20, 54], [0, 48, 47], [55, 24], [35, 54], [65, 1], []], ![[31, 9, 53, 4], [42, 22, 18, 15], [5, 40], [19, 29], [34, 64], [30, 35]], ![[9, 11, 43, 13], [7, 30, 14, 42], [59, 47], [20, 26], [37, 14], [4, 35]]]
 h' := ![![[37, 58, 54], [0, 49, 56], [40, 19, 39], [65, 39, 52], [6, 27, 56], [0, 0, 1], [0, 1]], ![[28, 8, 13], [5, 59, 12], [39, 48, 65], [11, 8, 43], [1, 56, 30], [6, 52, 8], [37, 58, 54]], ![[0, 1], [49, 26, 66], [61, 0, 30], [29, 20, 39], [42, 51, 48], [35, 15, 58], [28, 8, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66, 62], []]
 b := ![[], [49, 5, 46], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [3, 15, 2, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4757, 335, 335]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-71, 5, 5]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def PBC67 : ContainsPrimesAboveP 67 ![I67N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![67, 0, 0]]) timesTableT_eq_Table B_one_repr 67 (by decide) 𝕀

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


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [59, 55, 48, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 2, 53], [49, 68, 18], [0, 1]]
 g := ![![[57, 14, 16], [10, 38, 24], [67, 29, 36], [12, 32], [23, 1], []], ![[44, 50, 15, 28], [37, 59, 55, 67], [43, 48, 1, 33], [2, 37], [39, 9], [67, 40]], ![[42, 16, 68, 54], [30, 14, 15, 15], [33, 41, 70, 3], [12, 58], [51, 4], [31, 40]]]
 h' := ![![[45, 2, 53], [49, 9, 4], [23, 25, 38], [66, 34, 6], [63, 25, 48], [0, 0, 1], [0, 1]], ![[49, 68, 18], [55, 59, 39], [20, 49, 4], [39, 23, 9], [21, 45, 45], [60, 28, 68], [45, 2, 53]], ![[0, 1], [9, 3, 28], [51, 68, 29], [52, 14, 56], [60, 1, 49], [4, 43, 2], [49, 68, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 15], []]
 b := ![[], [28, 37, 60], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [59, 55, 48, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-694167, -80514, 24424]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9777, -1134, 344]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0]] 
 ![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [48, 20, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 43, 25], [25, 29, 48], [0, 1]]
 g := ![![[34, 45, 65], [60, 1], [9, 1], [16, 46, 69], [72, 1], []], ![[67, 11, 28, 27], [63, 41], [65, 64], [71, 50, 19, 18], [32, 38], [65, 41]], ![[4, 5, 18, 36], [2, 19], [72, 8], [26, 52, 29, 72], [61, 24], [42, 41]]]
 h' := ![![[47, 43, 25], [67, 19, 49], [63, 6, 72], [35, 68, 72], [48, 45, 54], [0, 0, 1], [0, 1]], ![[25, 29, 48], [48, 53, 71], [15, 68, 48], [54, 33, 65], [54, 4, 63], [38, 44, 29], [47, 43, 25]], ![[0, 1], [54, 1, 26], [71, 72, 26], [60, 45, 9], [8, 24, 29], [69, 29, 43], [25, 29, 48]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 28], []]
 b := ![[], [32, 7, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [48, 20, 1, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6132, 1533, -511]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-84, 21, -7]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def PBC73 : ContainsPrimesAboveP 73 ![I73N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![73, 0, 0]]) timesTableT_eq_Table B_one_repr 73 (by decide) 𝕀

instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![277, -73, 15]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![277, -73, 15]] 
 ![![79, 0, 0], ![0, 79, 0], ![29, 32, 1]] where
  M :=![![![277, -73, 15], ![-1050, 277, -58], ![4060, -1050, 219]]]
  hmulB := by decide  
  f := ![![![-3, 3, 1]], ![![-70, -3, 4]], ![![-33, -1, 2]]]
  g := ![![![-2, -7, 15], ![8, 27, -58], ![-29, -102, 219]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [36, 75, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 78], [0, 1]]
 g := ![![[35, 11], [19, 8], [72, 49], [41, 11], [16], [1]], ![[0, 68], [51, 71], [31, 30], [6, 68], [16], [1]]]
 h' := ![![[4, 78], [27, 13], [15, 18], [25, 7], [9, 13], [43, 4], [0, 1]], ![[0, 1], [0, 66], [8, 61], [53, 72], [61, 66], [59, 75], [4, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42]]
 b := ![[], [37, 21]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [36, 75, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-524, -205, 159]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-65, -67, 159]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -3, -1]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![3, -3, -1]] 
 ![![79, 0, 0], ![46, 1, 0], ![17, 0, 1]] where
  M :=![![![3, -3, -1], ![70, 3, -4], ![280, 70, -1]]]
  hmulB := by decide  
  f := ![![![-277, 73, -15]], ![![-148, 39, -8]], ![![-111, 29, -6]]]
  g := ![![![2, -3, -1], ![0, 3, -4], ![-37, 70, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![277, -73, 15]] ![![3, -3, -1]]
  ![![79, 0, 0]] where
 M := ![![![-79, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB103I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB103I1 : PrimesBelowBoundCertificateInterval O 31 79 103 where
  m := 11
  g := ![3, 3, 2, 1, 2, 3, 1, 1, 1, 1, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB103I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0]
    · exact ![I67N0]
    · exact ![I71N0]
    · exact ![I73N0]
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
    · exact ![1849, 43]
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![59, 59, 59]
    · exact ![226981]
    · exact ![300763]
    · exact ![357911]
    · exact ![389017]
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
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N0, I37N1, I37N2, I41N0, I41N1, I43N1, I53N1, I59N0, I59N1, I59N2, I79N1]
  Il := ![[I37N0, I37N1, I37N2], [I41N0, I41N0, I41N1], [I43N1], [], [I53N1], [I59N0, I59N1, I59N2], [], [], [], [], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
