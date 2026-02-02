// IMP verifier with partial programs and obligations
// Based on: Partial Programs with Obligations (SPEC.md)

import java.io._
import scala.sys.process._

// AST definitions
sealed trait AExpr
case class Num(n: Int) extends AExpr
case class Var(x: String) extends AExpr
case class Plus(a1: AExpr, a2: AExpr) extends AExpr
case class Minus(a1: AExpr, a2: AExpr) extends AExpr
case class Times(a1: AExpr, a2: AExpr) extends AExpr

sealed trait BExpr
case object True extends BExpr
case object False extends BExpr
case class Eq(a1: AExpr, a2: AExpr) extends BExpr
case class Lt(a1: AExpr, a2: AExpr) extends BExpr
case class Leq(a1: AExpr, a2: AExpr) extends BExpr
case class Not(b: BExpr) extends BExpr
case class And(b1: BExpr, b2: BExpr) extends BExpr
case class Or(b1: BExpr, b2: BExpr) extends BExpr
case class Implies(b1: BExpr, b2: BExpr) extends BExpr

sealed trait Stmt
case object Skip extends Stmt
case class Assign(x: String, a: AExpr) extends Stmt
case class Seq(s1: Stmt, s2: Stmt) extends Stmt
case class If(b: BExpr, s1: Stmt, s2: Stmt) extends Stmt
case class While(b: BExpr, inv: BExpr, s: Stmt) extends Stmt
case class Assert(p: BExpr) extends Stmt
case class Assume(p: BExpr) extends Stmt
case class Hole(id: Int) extends Stmt  // □ with unique id for tracking

case class Program(pre: BExpr, stmt: Stmt, post: BExpr)

// An obligation: a Hoare triple that a hole-filling must satisfy
case class Obligation(holeId: Int, pre: BExpr, post: BExpr)

// Verification condition generation with obligations for partial programs
object Verifier {

  def substitute(e: AExpr, x: String, a: AExpr): AExpr = e match {
    case Num(n) => Num(n)
    case Var(y) => if (x == y) a else Var(y)
    case Plus(a1, a2) => Plus(substitute(a1, x, a), substitute(a2, x, a))
    case Minus(a1, a2) => Minus(substitute(a1, x, a), substitute(a2, x, a))
    case Times(a1, a2) => Times(substitute(a1, x, a), substitute(a2, x, a))
  }

  def substitute(b: BExpr, x: String, a: AExpr): BExpr = b match {
    case True => True
    case False => False
    case Eq(a1, a2) => Eq(substitute(a1, x, a), substitute(a2, x, a))
    case Lt(a1, a2) => Lt(substitute(a1, x, a), substitute(a2, x, a))
    case Leq(a1, a2) => Leq(substitute(a1, x, a), substitute(a2, x, a))
    case Not(b1) => Not(substitute(b1, x, a))
    case And(b1, b2) => And(substitute(b1, x, a), substitute(b2, x, a))
    case Or(b1, b2) => Or(substitute(b1, x, a), substitute(b2, x, a))
    case Implies(b1, b2) => Implies(substitute(b1, x, a), substitute(b2, x, a))
  }

  // Combined wp and vcgen for partial programs
  // p = precondition (threaded forward), q = postcondition (threaded backward via WP)
  // Returns (weakest precondition, verification conditions, obligations)
  def wpVc(s: Stmt, p: BExpr, q: BExpr): (BExpr, List[BExpr], List[Obligation]) = s match {
    case Skip =>
      (q, Nil, Nil)

    case Assign(x, a) =>
      (substitute(q, x, a), Nil, Nil)

    case Seq(s1, s2) =>
      val (wp2, vcs2, obs2) = wpVc(s2, p, q)  // p is approximate here; refined below
      val (wp1, vcs1, obs1) = wpVc(s1, p, wp2)
      // The precondition for s2 is the WP of s1 (what holds after s1)
      val (_, vcs2r, obs2r) = wpVc(s2, wp1, q)
      (wp1, vcs1 ++ vcs2r, obs1 ++ obs2r)

    case If(b, s1, s2) =>
      val (wp1, vcs1, obs1) = wpVc(s1, And(p, b), q)
      val (wp2, vcs2, obs2) = wpVc(s2, And(p, Not(b)), q)
      (And(Implies(b, wp1), Implies(Not(b), wp2)), vcs1 ++ vcs2, obs1 ++ obs2)

    case While(b, inv, s) =>
      val (wpBody, vcsBody, obsBody) = wpVc(s, And(inv, b), inv)
      val vcInv = Implies(And(inv, b), wpBody)  // invariant preserved
      val vcExit = Implies(And(inv, Not(b)), q) // exit condition
      (inv, vcInv :: vcExit :: vcsBody, obsBody)

    case Assert(pr) =>
      (And(q, pr), Nil, Nil)

    case Assume(pr) =>
      (Implies(pr, q), Nil, Nil)

    case Hole(id) =>
      // {P} □ {Q} ▷ { {P} □ {Q} }
      // P is the precondition at this program point, Q is the required postcondition.
      (q, Nil, List(Obligation(id, p, q)))
  }

  // Result of partial verification: Γ ⊢ {P} c {Q} ▷ O
  case class PartialResult(
    vcs: List[BExpr],           // standard verification conditions (must all hold)
    obligations: List[Obligation] // hole obligations (for completions to discharge)
  )

  def verify(prog: Program): PartialResult = {
    val (wp, vcs, obligations) = wpVc(prog.stmt, prog.pre, prog.post)
    val mainVc = Implies(prog.pre, wp)
    PartialResult(mainVc :: vcs, obligations)
  }

  // Fill holes in a statement with concrete commands
  def fillHoles(s: Stmt, fillings: Map[Int, Stmt]): Stmt = s match {
    case Skip => Skip
    case Assign(x, a) => Assign(x, a)
    case Seq(s1, s2) => Seq(fillHoles(s1, fillings), fillHoles(s2, fillings))
    case If(b, s1, s2) => If(b, fillHoles(s1, fillings), fillHoles(s2, fillings))
    case While(b, inv, s) => While(b, inv, fillHoles(s, fillings))
    case Assert(p) => Assert(p)
    case Assume(p) => Assume(p)
    case Hole(id) => fillings.getOrElse(id, Hole(id))
  }

  // Check that a completion discharges all obligations
  def verifyCompletion(prog: Program, fillings: Map[Int, Stmt]): PartialResult = {
    val completed = prog.copy(stmt = fillHoles(prog.stmt, fillings))
    verify(completed)
  }
}

// SMT-LIB generation
object SMTLib {
  
  def toSMT(e: AExpr): String = e match {
    case Num(n) => n.toString
    case Var(x) => x
    case Plus(a1, a2) => s"(+ ${toSMT(a1)} ${toSMT(a2)})"
    case Minus(a1, a2) => s"(- ${toSMT(a1)} ${toSMT(a2)})"
    case Times(a1, a2) => s"(* ${toSMT(a1)} ${toSMT(a2)})"
  }
  
  def toSMT(b: BExpr): String = b match {
    case True => "true"
    case False => "false"
    case Eq(a1, a2) => s"(= ${toSMT(a1)} ${toSMT(a2)})"
    case Lt(a1, a2) => s"(< ${toSMT(a1)} ${toSMT(a2)})"
    case Leq(a1, a2) => s"(<= ${toSMT(a1)} ${toSMT(a2)})"
    case Not(b1) => s"(not ${toSMT(b1)})"
    case And(b1, b2) => s"(and ${toSMT(b1)} ${toSMT(b2)})"
    case Or(b1, b2) => s"(or ${toSMT(b1)} ${toSMT(b2)})"
    case Implies(b1, b2) => s"(=> ${toSMT(b1)} ${toSMT(b2)})"
  }
  
  def freeVars(e: AExpr): Set[String] = e match {
    case Num(_) => Set.empty
    case Var(x) => Set(x)
    case Plus(a1, a2) => freeVars(a1) ++ freeVars(a2)
    case Minus(a1, a2) => freeVars(a1) ++ freeVars(a2)
    case Times(a1, a2) => freeVars(a1) ++ freeVars(a2)
  }
  
  def freeVars(b: BExpr): Set[String] = b match {
    case True | False => Set.empty
    case Eq(a1, a2) => freeVars(a1) ++ freeVars(a2)
    case Lt(a1, a2) => freeVars(a1) ++ freeVars(a2)
    case Leq(a1, a2) => freeVars(a1) ++ freeVars(a2)
    case Not(b1) => freeVars(b1)
    case And(b1, b2) => freeVars(b1) ++ freeVars(b2)
    case Or(b1, b2) => freeVars(b1) ++ freeVars(b2)
    case Implies(b1, b2) => freeVars(b1) ++ freeVars(b2)
  }
}

// Z3 integration
object Z3Runner {
  def checkSat(smtScript: String): (Boolean, String) = {
    val tempFile = File.createTempFile("imp_vc_", ".smt2")
    try {
      val writer = new PrintWriter(tempFile)
      writer.write(smtScript)
      writer.close()
      
      val result = Process(scala.Seq("z3", tempFile.getAbsolutePath)).!!
      val lines = result.trim.split("\n")
      
      val isSat = lines.headOption.contains("sat")
      val isUnsat = lines.headOption.contains("unsat")
      (isSat || !isUnsat, result) // unknown are treated cautiously as sat
    } finally {
      tempFile.delete()
    }
  }
  
  def parseModel(output: String): Map[String, Int] = {
    val modelPattern = "\\(define-fun\\s+(\\w+)\\s+\\(\\)\\s+Int\\s+(\\(-\\s+\\d+\\)|\\d+)\\)".r
    val negPattern = "\\(-\\s+(\\d+)\\)".r
    modelPattern.findAllMatchIn(output).map { m =>
      val varName = m.group(1)
      val valueExpr = m.group(2)

      val value = valueExpr match {
        case negPattern(num) => -num.toInt
        case num => num.toInt
      }
      varName -> value
    }.toMap
  }
  
  def verifyVC(vc: BExpr, vars: Set[String]): (Boolean, String, String) = {
    val smtScript = checkVC(vc, vars)
    val (isSat, output) = checkSat(smtScript)
    (!isSat, output, smtScript) // VC is valid if negation is UNSAT
  }
  
  def checkVC(vc: BExpr, vars: Set[String]): String = {
    val declarations = vars.toList.sorted.map(v => s"(declare-fun $v () Int)").mkString("\n")
    
    s"""(set-logic QF_NIA)
       |$declarations
       |(assert (not ${SMTLib.toSMT(vc)}))
       |(check-sat)""".stripMargin
  }
  
  def verifyAll(vcs: List[BExpr]): List[(BExpr, String, Boolean, String, Option[Map[String, Int]])] = {
    val vars = vcs.flatMap(SMTLib.freeVars).toSet
    vcs.map { vc =>
      val (isValid, output, smtScript) = verifyVC(vc, vars)
      val model = if (!isValid && output.contains("sat")) {
        // Get model by running a separate query
        val modelScript = s"""${checkVC(vc, vars)}
                             |(get-model)""".stripMargin
        val (_, modelOutput) = checkSat(modelScript)
        Some(parseModel(modelOutput))
      } else None
      (vc, smtScript, isValid, output, model)
    }
  }
}

// Pretty printing
object PP {
  def pp(b: BExpr): String = b match {
    case True => "true"
    case False => "false"
    case Eq(a1, a2) => s"${pp(a1)} = ${pp(a2)}"
    case Lt(a1, a2) => s"${pp(a1)} < ${pp(a2)}"
    case Leq(a1, a2) => s"${pp(a1)} <= ${pp(a2)}"
    case Not(b1) => s"!${pp(b1)}"
    case And(b1, b2) => s"(${pp(b1)} && ${pp(b2)})"
    case Or(b1, b2) => s"(${pp(b1)} || ${pp(b2)})"
    case Implies(b1, b2) => s"(${pp(b1)} => ${pp(b2)})"
  }

  def pp(a: AExpr): String = a match {
    case Num(n) => n.toString
    case Var(x) => x
    case Plus(a1, a2) => s"${pp(a1)} + ${pp(a2)}"
    case Minus(a1, a2) => s"${pp(a1)} - ${pp(a2)}"
    case Times(a1, a2) => s"${pp(a1)} * ${pp(a2)}"
  }

  def pp(s: Stmt, indent: Int = 0): String = {
    val sp = "  " * indent
    s match {
      case Skip => s"${sp}skip"
      case Assign(x, a) => s"${sp}$x := ${pp(a)}"
      case Seq(s1, s2) => s"${pp(s1, indent)};\n${pp(s2, indent)}"
      case If(b, s1, s2) =>
        s"${sp}if (${pp(b)}) then\n${pp(s1, indent + 1)}\n${sp}else\n${pp(s2, indent + 1)}"
      case While(b, inv, s) =>
        s"${sp}while (${pp(b)})\n${sp}  inv: ${pp(inv)}\n${sp}do\n${pp(s, indent + 1)}"
      case Assert(p) => s"${sp}assert(${pp(p)})"
      case Assume(p) => s"${sp}assume(${pp(p)})"
      case Hole(id) => s"${sp}[□$id]"
    }
  }

  def pp(prog: Program): String = {
    s"pre:  ${pp(prog.pre)}\n" +
    s"${pp(prog.stmt)}\n" +
    s"post: ${pp(prog.post)}"
  }

  def pp(ob: Obligation): String =
    s"{${pp(ob.pre)}} □${ob.holeId} {${pp(ob.post)}}"
}

// Example programs and main
object Main extends App {
  import PP._

  // === Standard examples (no holes) ===

  val maxProgram = Program(
    True,
    If(Lt(Var("x"), Var("y")),
       Assign("m", Var("y")),
       Assign("m", Var("x"))),
    And(Or(Eq(Var("m"), Var("x")), Eq(Var("m"), Var("y"))),
        And(Leq(Var("x"), Var("m")), Leq(Var("y"), Var("m"))))
  )

  val loopProgram = Program(
    And(And(Eq(Var("i"), Num(0)), Eq(Var("s"), Num(0))), Leq(Num(0), Var("n"))),
    While(
      Lt(Var("i"), Var("n")),
      And(Leq(Num(0), Var("i")), Leq(Var("i"), Var("n"))),
      Seq(
        Assign("s", Plus(Var("s"), Var("i"))),
        Assign("i", Plus(Var("i"), Num(1)))
      )
    ),
    Eq(Var("i"), Var("n"))
  )

  val maxProgramBogus = Program(
    True,
    If(Lt(Var("x"), Var("y")),
      Assign("m", Var("y")),
      Assign("m", Var("x"))),
    Eq(Var("m"), Var("x"))
  )

  // === Partial programs (with holes) ===

  // Hole in the else branch of max: what should we assign to m when x >= y?
  val maxWithHole = Program(
    True,
    If(Lt(Var("x"), Var("y")),
       Assign("m", Var("y")),
       Hole(0)),
    And(Or(Eq(Var("m"), Var("x")), Eq(Var("m"), Var("y"))),
        And(Leq(Var("x"), Var("m")), Leq(Var("y"), Var("m"))))
  )

  // Hole for loop body: what should the body do?
  val loopWithHole = Program(
    And(Eq(Var("i"), Num(0)), Leq(Num(0), Var("n"))),
    While(
      Lt(Var("i"), Var("n")),
      And(Leq(Num(0), Var("i")), Leq(Var("i"), Var("n"))),
      Hole(0)
    ),
    Eq(Var("i"), Var("n"))
  )

  // Two holes: both branches unknown
  val maxTwoHoles = Program(
    True,
    If(Lt(Var("x"), Var("y")),
       Hole(0),
       Hole(1)),
    And(Or(Eq(Var("m"), Var("x")), Eq(Var("m"), Var("y"))),
        And(Leq(Var("x"), Var("m")), Leq(Var("y"), Var("m"))))
  )

  // Hole after assignment: init + □ + postcondition
  val seqWithHole = Program(
    True,
    Seq(Assign("x", Num(0)), Hole(0)),
    Eq(Var("x"), Num(1))
  )

  def verifyProgram(name: String, prog: Program): Unit = {
    println(s"\n${"=" * 50}")
    println(s"=== $name ===")
    println(s"${"=" * 50}")
    println(s"\n${pp(prog)}")

    val result = Verifier.verify(prog)

    // Build unified list of labeled items: VCs and obligations
    sealed trait Item { def expr: BExpr }
    case class VCItem(index: Int, expr: BExpr) extends Item
    case class ObItem(ob: Obligation, expr: BExpr) extends Item

    val vcItems = result.vcs.zipWithIndex.map { case (vc, i) => VCItem(i + 1, vc) }
    val obItems = result.obligations.map { ob => ObItem(ob, Implies(ob.pre, ob.post)) }
    val allItems: List[Item] = vcItems ++ obItems

    println(s"\nChecks (${allItems.length}):")
    allItems.foreach {
      case VCItem(i, vc) =>
        println(s"  [VC$i]                ${pp(vc)}")
      case ObItem(ob, _) =>
        val pad = " " * (19 - s"OBLIGATION for □${ob.holeId}".length).max(1)
        println(s"  [OBLIGATION for □${ob.holeId}]${pad}${pp(ob)}")
    }

    try {
      println(s"\nZ3 Verification:")
      println("-" * 40)
      val z3Results = Z3Runner.verifyAll(allItems.map(_.expr))
      var failureCount = 0

      z3Results.zip(allItems).foreach { case ((_, _, isValid, _, model), item) =>
        val label = item match {
          case VCItem(i, _) => s"VC$i"
          case ObItem(ob, _) => s"OBLIGATION for □${ob.holeId}"
        }
        if (isValid) {
          println(s"  $label: VALID")
        } else {
          failureCount += 1
          println(s"  $label: INVALID")
          println(s"    Failed: ${pp(item.expr)}")
          model.foreach { m =>
            if (m.nonEmpty) {
              println("    Counterexample:")
              m.toList.sortBy(_._1).foreach { case (v, n) =>
                println(s"      $v = $n")
              }
            }
          }
        }
      }

      println()
      if (result.obligations.nonEmpty && failureCount == 0) {
        println(s"PARTIAL: $name verified modulo ${result.obligations.length} obligation(s)")
      } else if (failureCount == 0) {
        println(s"VERIFIED: $name")
      } else {
        println(s"FAILED: $name ($failureCount invalid VC(s))")
      }
    } catch {
      case e: Exception =>
        println(s"Error running Z3: ${e.getMessage}")
        println("Make sure Z3 is installed and in your PATH")
    }
  }

  def verifyCompletion(name: String, prog: Program, fillings: Map[Int, Stmt]): Unit = {
    println(s"\n${"=" * 50}")
    println(s"=== Completing $name ===")
    println(s"${"=" * 50}")
    println(s"\nOriginal:\n${pp(prog)}")
    println(s"\nFillings:")
    fillings.foreach { case (id, s) => println(s"  □$id -> ${pp(s)}") }

    val completed = prog.copy(stmt = Verifier.fillHoles(prog.stmt, fillings))
    println(s"\nCompleted:\n${pp(completed)}")

    val result = Verifier.verify(completed)
    assert(result.obligations.isEmpty, "Completed program still has holes!")

    println(s"\nVerification conditions (${result.vcs.length}):")
    result.vcs.zipWithIndex.foreach { case (vc, i) =>
      println(s"  VC${i+1}: ${pp(vc)}")
    }

    try {
      println(s"\nZ3 Verification:")
      println("-" * 40)
      val results = Z3Runner.verifyAll(result.vcs)
      var failureCount = 0

      results.zipWithIndex.foreach { case ((vc, _, isValid, _, model), i) =>
        if (isValid) {
          println(s"  VC${i+1}: VALID")
        } else {
          failureCount += 1
          println(s"  VC${i+1}: INVALID")
          println(s"    Failed: ${pp(vc)}")
          model.foreach { m =>
            if (m.nonEmpty) {
              println("    Counterexample:")
              m.toList.sortBy(_._1).foreach { case (v, n) => println(s"      $v = $n") }
            }
          }
        }
      }

      println()
      if (failureCount == 0) println(s"VERIFIED: completion of $name")
      else println(s"FAILED: completion of $name ($failureCount invalid VC(s))")
    } catch {
      case e: Exception =>
        println(s"Error running Z3: ${e.getMessage}")
    }
  }

  // Run standard examples
  verifyProgram("Max", maxProgram)
  verifyProgram("Loop", loopProgram)
  verifyProgram("MaxBogus", maxProgramBogus)

  // Run partial program examples
  verifyProgram("MaxWithHole", maxWithHole)
  verifyProgram("LoopWithHole", loopWithHole)
  verifyProgram("MaxTwoHoles", maxTwoHoles)
  verifyProgram("SeqWithHole", seqWithHole)

  // Verify completions: fill the holes and check soundness
  verifyCompletion("MaxWithHole", maxWithHole,
    Map(0 -> Assign("m", Var("x"))))  // correct filling

  verifyCompletion("MaxWithHole (wrong)", maxWithHole,
    Map(0 -> Assign("m", Var("y"))))  // wrong filling: m := y when x >= y

  verifyCompletion("LoopWithHole", loopWithHole,
    Map(0 -> Assign("i", Plus(Var("i"), Num(1)))))  // correct: i := i + 1

  verifyCompletion("MaxTwoHoles", maxTwoHoles,
    Map(0 -> Assign("m", Var("y")), 1 -> Assign("m", Var("x"))))

  verifyCompletion("SeqWithHole", seqWithHole,
    Map(0 -> Assign("x", Plus(Var("x"), Num(1)))))  // x := x + 1
}
