import Base
import ../web/json.bend as J
import ../web/store.bend as St
import ../web/api.bend as A
import ./logic.bend as L
import ./web.bend as PW
import ./auth.bend as PA

# Proofs about rotating and revoking organization keys. LAWS.bend states the
# rules; these prove them.

def MO() -> Data:
  Maybe<&2, St.Org>

# Text.same meets
# ---------------

# Two texts that each match a third match each other. Text.same compares
# character codes, so this holds without knowing that equal codes are equal
# characters.
law nat_meet:
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for ex: {Nat.is_eq(x, z) == True{} : Bool}
  for ey: {Nat.is_eq(y, z) == True{} : Bool}
  {Nat.is_eq(x, y) == True{} : Bool}

def nat_meet(x, y, z, ex, ey):
  %Equal.sym(Nat, x, z, L.eq_of(x, z, ex)) : {Nat.is_eq(_, y) == True{} : Bool}
  %Equal.sym(Nat, y, z, L.eq_of(y, z, ey)) : {Nat.is_eq(z, _) == True{} : Bool}
  L.eq_refl(z)

law same_meet:
  for +c: String
  for +a: String
  for +b: String
  for +ea: {J.Text.same(a, c) == True{} : Bool}
  for +eb: {J.Text.same(b, c) == True{} : Bool}
  {J.Text.same(a, b) == True{} : Bool}

def same_meet(c, a, b, ea, eb):
  match c a b:
    case SNil{} SNil{} SNil{}:
      {==}
    case SNil{} SNil{} SCon{y, bt}:
      L.never({J.Text.same(SNil{}, SCon{y, bt}) == True{} : Bool}, eb)
    case SNil{} SCon{x, at} SNil{}:
      L.never({J.Text.same(SCon{x, at}, SNil{}) == True{} : Bool}, ea)
    case SNil{} SCon{x, at} SCon{y, bt}:
      L.never({J.Text.same(SCon{x, at}, SCon{y, bt}) == True{} : Bool}, ea)
    case SCon{z, ct} SNil{} SNil{}:
      L.never({J.Text.same(SNil{}, SNil{}) == True{} : Bool}, ea)
    case SCon{z, ct} SNil{} SCon{y, bt}:
      L.never({J.Text.same(SNil{}, SCon{y, bt}) == True{} : Bool}, ea)
    case SCon{z, ct} SCon{x, at} SNil{}:
      L.never({J.Text.same(SCon{x, at}, SNil{}) == True{} : Bool}, eb)
    case SCon{z, ct} SCon{x, at} SCon{y, bt}:
      L.and_i(Nat.is_eq(J.Text.code(x), J.Text.code(y)), J.Text.same(at, bt),
        nat_meet(J.Text.code(x), J.Text.code(y), J.Text.code(z),
          L.and_l(Nat.is_eq(J.Text.code(x), J.Text.code(z)), J.Text.same(at, ct), ea),
          L.and_l(Nat.is_eq(J.Text.code(y), J.Text.code(z)), J.Text.same(bt, ct), eb)),
        same_meet(ct, at, bt,
          L.and_r(Nat.is_eq(J.Text.code(x), J.Text.code(z)), J.Text.same(at, ct), ea),
          L.and_r(Nat.is_eq(J.Text.code(y), J.Text.code(z)), J.Text.same(bt, ct), eb)))

# Dropping an organization
# ------------------------

law drop_holds_pick:
  for +b: Bool
  for +i: String
  for +h: String
  for +g: St.Org
  for +rest: List<&2, St.Org>
  for eb: {J.Text.same(i, St.Org.id(g)) == b : Bool}
  for ih: {St.Orgs.holds(i, h, St.Orgs.drop(i, rest)) == False{} : Bool}
  {St.Orgs.holds(i, h, St.Orgs.drop.pick(b, g, St.Orgs.drop(i, rest))) == False{} : Bool}

def drop_holds_pick(b, i, h, g, rest, eb, ih):
  match b:
    case True{}:
      ih
    case False{}:
      %Equal.sym(Bool, J.Text.same(i, St.Org.id(g)), False{}, eb) : {Bool.or(Bool.and(_, J.Text.same(h, St.Org.hash(g))), St.Orgs.holds(i, h, St.Orgs.drop(i, rest))) == False{} : Bool}
      ih

# Once an id is dropped, no key belongs to it.
law drop_holds:
  for +i: String
  for +h: String
  for +gs: List<&2, St.Org>
  {St.Orgs.holds(i, h, St.Orgs.drop(i, gs)) == False{} : Bool}

def drop_holds(i, h, gs):
  match gs:
    case Nil{}:
      {==}
    case Con{g, rest}:
      drop_holds_pick(J.Text.same(i, St.Org.id(g)), i, h, g, rest, {==}, drop_holds(i, h, rest))

law drop_find_pick:
  for +b: Bool
  for +i: String
  for +g: St.Org
  for +rest: List<&2, St.Org>
  for eb: {J.Text.same(i, St.Org.id(g)) == b : Bool}
  for ih: {St.Orgs.find(i, St.Orgs.drop(i, rest)) == None{} : MO()}
  {St.Orgs.find(i, St.Orgs.drop.pick(b, g, St.Orgs.drop(i, rest))) == None{} : MO()}

def drop_find_pick(b, i, g, rest, eb, ih):
  match b:
    case True{}:
      ih
    case False{}:
      %Equal.sym(Bool, J.Text.same(i, St.Org.id(g)), False{}, eb) : {St.Orgs.pick(_, g, St.Orgs.find(i, St.Orgs.drop(i, rest))) == None{} : MO()}
      ih

# And no organization is found under it.
law drop_find:
  for +i: String
  for +gs: List<&2, St.Org>
  {St.Orgs.find(i, St.Orgs.drop(i, gs)) == None{} : MO()}

def drop_find(i, gs):
  match gs:
    case Nil{}:
      {==}
    case Con{g, rest}:
      drop_find_pick(J.Text.same(i, St.Org.id(g)), i, g, rest, {==}, drop_find(i, rest))

law keeps_hit:
  for +c: Bool
  for +j: String
  for +i: String
  for +h: String
  for +g: St.Org
  for +rest: List<&2, St.Org>
  for ne: {J.Text.same(j, i) == False{} : Bool}
  for ei: {J.Text.same(i, St.Org.id(g)) == True{} : Bool}
  for ec: {J.Text.same(j, St.Org.id(g)) == c : Bool}
  for ih: {St.Orgs.holds(j, h, St.Orgs.drop(i, rest)) == St.Orgs.holds(j, h, rest) : Bool}
  {St.Orgs.holds(j, h, St.Orgs.drop(i, rest)) == St.Orgs.holds(j, h, g <> rest) : Bool}

def keeps_hit(c, j, i, h, g, rest, ne, ei, ec, ih):
  match c:
    case True{}:
      L.clash(J.Text.same(j, i), {St.Orgs.holds(j, h, St.Orgs.drop(i, rest)) == St.Orgs.holds(j, h, g <> rest) : Bool},
        same_meet(St.Org.id(g), j, i, ec, ei), ne)
    case False{}:
      %Equal.sym(Bool, J.Text.same(j, St.Org.id(g)), False{}, ec) : {St.Orgs.holds(j, h, St.Orgs.drop(i, rest)) == Bool.or(Bool.and(_, J.Text.same(h, St.Org.hash(g))), St.Orgs.holds(j, h, rest)) : Bool}
      ih

law keeps_pick:
  for +b: Bool
  for +j: String
  for +i: String
  for +h: String
  for +g: St.Org
  for +rest: List<&2, St.Org>
  for ne: {J.Text.same(j, i) == False{} : Bool}
  for eb: {J.Text.same(i, St.Org.id(g)) == b : Bool}
  for ih: {St.Orgs.holds(j, h, St.Orgs.drop(i, rest)) == St.Orgs.holds(j, h, rest) : Bool}
  {St.Orgs.holds(j, h, St.Orgs.drop.pick(b, g, St.Orgs.drop(i, rest))) == St.Orgs.holds(j, h, g <> rest) : Bool}

def keeps_pick(b, j, i, h, g, rest, ne, eb, ih):
  match b:
    case True{}:
      keeps_hit(J.Text.same(j, St.Org.id(g)), j, i, h, g, rest, ne, eb, {==}, ih)
    case False{}:
      %ih : {Bool.or(Bool.and(J.Text.same(j, St.Org.id(g)), J.Text.same(h, St.Org.hash(g))), St.Orgs.holds(j, h, St.Orgs.drop(i, rest))) == Bool.or(Bool.and(J.Text.same(j, St.Org.id(g)), J.Text.same(h, St.Org.hash(g))), _) : Bool}
      {==}

# Dropping one id leaves every other id's keys as they were.
law drop_keeps:
  for +j: String
  for +i: String
  for +h: String
  for +gs: List<&2, St.Org>
  for +ne: {J.Text.same(j, i) == False{} : Bool}
  {St.Orgs.holds(j, h, St.Orgs.drop(i, gs)) == St.Orgs.holds(j, h, gs) : Bool}

def drop_keeps(j, i, h, gs, ne):
  match gs:
    case Nil{}:
      {==}
    case Con{g, rest}:
      keeps_pick(J.Text.same(i, St.Org.id(g)), j, i, h, g, rest, ne, {==}, drop_keeps(j, i, h, rest, ne))

# Finding an organization
# -----------------------

def org_of(m: MO()) -> St.Org:
  match m:
    case Some{g}:
      g
    case None{}:
      St.Org{"", "", ""}

law find_pick:
  for +b: Bool
  for +i: String
  for +x: St.Org
  for +rest: List<&2, St.Org>
  for +g: St.Org
  for eb: {J.Text.same(i, St.Org.id(x)) == b : Bool}
  for e: {St.Orgs.pick(b, x, St.Orgs.find(i, rest)) == Some{g} : MO()}
  for ih: {St.Orgs.find(i, rest) == Some{g} : MO()} -> {J.Text.same(i, St.Org.id(g)) == True{} : Bool}
  {J.Text.same(i, St.Org.id(g)) == True{} : Bool}

def find_pick(b, i, x, rest, g, eb, e, ih):
  match b:
    case True{}:
      %Equal.cong(MO(), St.Org, m => org_of(m), Some{x}, Some{g}, e) : {J.Text.same(i, St.Org.id(_)) == True{} : Bool}
      eb
    case False{}:
      ih(e)

# The organization found under an id has that id.
law find_same:
  for +i: String
  for +gs: List<&2, St.Org>
  for +g: St.Org
  for e: {St.Orgs.find(i, gs) == Some{g} : MO()}
  {J.Text.same(i, St.Org.id(g)) == True{} : Bool}

def find_same(i, gs, g, e):
  match gs:
    case Nil{}:
      L.never({J.Text.same(i, St.Org.id(g)) == True{} : Bool}, Equal.cong(MO(), Bool, m => Maybe.is_some(&2, St.Org, m), None{}, Some{g}, e))
    case Con{x, rest}:
      find_pick(J.Text.same(i, St.Org.id(x)), i, x, rest, g, {==}, e, q => find_same(i, rest, g, q))

law org_pick_same:
  for +live: MO()
  for +gone: MO()
  for +i: String
  for +g: St.Org
  for e: {St.Store.org.pick(live, gone) == Some{g} : MO()}
  for tl: {live == Some{g} : MO()} -> {J.Text.same(i, St.Org.id(g)) == True{} : Bool}
  for tg: {gone == Some{g} : MO()} -> {J.Text.same(i, St.Org.id(g)) == True{} : Bool}
  {J.Text.same(i, St.Org.id(g)) == True{} : Bool}

def org_pick_same(live, gone, i, g, e, tl, tg):
  match live:
    case Some{x}:
      tl(e)
    case None{}:
      tg(e)

# The organization Store.org finds, active or revoked, has the id it was
# asked for.
law store_org_same:
  for +i: String
  for +s: St.Store
  for +g: St.Org
  for e: {St.Store.org(i, s) == Some{g} : MO()}
  {J.Text.same(i, St.Org.id(g)) == True{} : Bool}

def store_org_same(i, s, g, e):
  match s:
    case St.Store{n, rs, m, gs, rt}:
      org_pick_same(St.Orgs.find(i, gs), St.Orgs.find(i, rt), i, g, e, q => find_same(i, gs, g, q), q => find_same(i, rt, g, q))

# Resolving
# ---------

def rotated(x: A.Resolved) -> MO():
  match x:
    case A.Handle{A.Rotate{f, k, h}}:
      f
    case other:
      None{}

def rotated_key(x: A.Resolved) -> String:
  match x:
    case A.Handle{A.Rotate{f, k, h}}:
      k
    case other:
      ""

def rotated_hash(x: A.Resolved) -> String:
  match x:
    case A.Handle{A.Rotate{f, k, h}}:
      h
    case other:
      ""

def revoked(x: A.Resolved) -> MO():
  match x:
    case A.Handle{A.Revoke{l, y}}:
      l
    case other:
      None{}

law rotate_found.key:
  for +key: Maybe<&2, String>
  for +q: St.Org
  for +g: St.Org
  for +k: String
  for +h: String
  for e: {A.Api.rotate(key, Some{q}) == A.Handle{A.Rotate{Some{g}, k, h}} : A.Resolved}
  {Some{q} == Some{g} : MO()}

def rotate_found.key(key, q, g, k, h, e):
  match key:
    case None{}:
      L.never({Some{q} == Some{g} : MO()}, Equal.cong(A.Resolved, Bool, x => PA.is_handle(x), A.Refuse{A.ServerError{}, "no_entropy"}, A.Handle{A.Rotate{Some{g}, k, h}}, e))
    case Some{p}:
      Equal.cong(A.Resolved, MO(), x => rotated(x), A.Api.rotate(Some{p}, Some{q}), A.Handle{A.Rotate{Some{g}, k, h}}, e)

law rotate_found:
  for +key: Maybe<&2, String>
  for +f: MO()
  for +g: St.Org
  for +k: String
  for +h: String
  for e: {A.Api.rotate(key, f) == A.Handle{A.Rotate{Some{g}, k, h}} : A.Resolved}
  {f == Some{g} : MO()}

def rotate_found(key, f, g, k, h, e):
  match f:
    case None{}:
      Equal.cong(A.Resolved, MO(), x => rotated(x), A.Api.rotate(key, None{}), A.Handle{A.Rotate{Some{g}, k, h}}, e)
    case Some{q}:
      rotate_found.key(key, q, g, k, h, e)

law rotate_found_is_named:
  for +ps: List<&2, String>
  for +body: String
  for +s: St.Store
  for +o: String
  for +seed: List<&2, U32>
  for +g: St.Org
  for +k: String
  for +h: String
  for e: {A.Api.resolve(A.ERotate{}, ps, body, s, o, seed) == A.Handle{A.Rotate{Some{g}, k, h}} : A.Resolved}
  {J.Text.same(A.Path.first(ps), St.Org.id(g)) == True{} : Bool}

def rotate_found_is_named(ps, body, s, o, seed, g, k, h, e):
  store_org_same(A.Path.first(ps), s, g, rotate_found(A.Key.of(seed), St.Store.org(A.Path.first(ps), s), g, k, h, e))

law revoke_found_is_named:
  for +ps: List<&2, String>
  for +body: String
  for +s: St.Store
  for +o: String
  for +seed: List<&2, U32>
  for +g: St.Org
  for +y: MO()
  for e: {A.Api.resolve(A.ERevoke{}, ps, body, s, o, seed) == A.Handle{A.Revoke{Some{g}, y}} : A.Resolved}
  {J.Text.same(A.Path.first(ps), St.Org.id(g)) == True{} : Bool}

def revoke_found_is_named(ps, body, s, o, seed, g, y, e):
  find_same(A.Path.first(ps), St.Store.orgs(s), g,
    Equal.cong(A.Resolved, MO(), x => revoked(x), A.Handle{A.Revoke{St.Orgs.find(A.Path.first(ps), St.Store.orgs(s)), St.Orgs.find(A.Path.first(ps), St.Store.retired(s))}}, A.Handle{A.Revoke{Some{g}, y}}, e))

# The store
# ---------

law rekey_signs_in:
  for +found: MO()
  for +s: St.Store
  for +i: String
  for +n: String
  for +h: String
  for +x: St.Org
  for e: {found == Some{x} : MO()}
  {A.Api.known(h, None{}, St.Store.orgs(St.Store.rekey(found, St.Org{i, n, h}, s))) == A.Dealer{i} : A.Who}

def rekey_signs_in(found, s, i, n, h, x, e):
  match found:
    case None{}:
      L.never({A.Api.known(h, None{}, St.Store.orgs(s)) == A.Dealer{i} : A.Who}, Equal.cong(MO(), Bool, m => Maybe.is_some(&2, St.Org, m), None{}, Some{x}, e))
    case Some{y}:
      match s:
        case St.Store{c, rs, m, gs, rt}:
          PA.new_key_signs_in(h, i, n, St.Orgs.drop(i, gs))

law rekey_beside_admin:
  for +found: MO()
  for +s: St.Store
  for +a: String
  for +i: String
  for +n: String
  for +h: String
  for +x: St.Org
  for e: {found == Some{x} : MO()}
  for +ne: {J.Text.same(h, a) == False{} : Bool}
  {A.Api.known(h, Some{a}, St.Store.orgs(St.Store.rekey(found, St.Org{i, n, h}, s))) == A.Dealer{i} : A.Who}

def rekey_beside_admin(found, s, a, i, n, h, x, e, ne):
  match found:
    case None{}:
      L.never({A.Api.known(h, Some{a}, St.Store.orgs(s)) == A.Dealer{i} : A.Who}, Equal.cong(MO(), Bool, m => Maybe.is_some(&2, St.Org, m), None{}, Some{x}, e))
    case Some{y}:
      match s:
        case St.Store{c, rs, m, gs, rt}:
          PA.new_key_beside_admin(h, a, i, n, St.Orgs.drop(i, gs), ne)

law old_key_false:
  for +i: String
  for +n: String
  for +h: String
  for +k: String
  for +gs: List<&2, St.Org>
  for +ne: {J.Text.same(k, h) == False{} : Bool}
  {St.Orgs.holds(i, k, St.Org{i, n, h} <> St.Orgs.drop(i, gs)) == False{} : Bool}

def old_key_false(i, n, h, k, gs, ne):
  %Equal.sym(Bool, J.Text.same(i, i), True{}, PW.same_refl(i)) : {Bool.or(Bool.and(_, J.Text.same(k, h)), St.Orgs.holds(i, k, St.Orgs.drop(i, gs))) == False{} : Bool}
  %Equal.sym(Bool, J.Text.same(k, h), False{}, ne) : {Bool.or(Bool.and(True{}, _), St.Orgs.holds(i, k, St.Orgs.drop(i, gs))) == False{} : Bool}
  drop_holds(i, k, gs)

law rekey_old_key:
  for +found: MO()
  for +s: St.Store
  for +i: String
  for +n: String
  for +h: String
  for +k: String
  for +admin: Maybe<&2, String>
  for +x: St.Org
  for ex: {found == Some{x} : MO()}
  for +ne: {J.Text.same(k, h) == False{} : Bool}
  for e: {A.Api.known(k, admin, St.Store.orgs(St.Store.rekey(found, St.Org{i, n, h}, s))) == A.Dealer{i} : A.Who}
  Empty

def rekey_old_key(found, s, i, n, h, k, admin, x, ex, ne, e):
  match found:
    case None{}:
      L.ff(Equal.cong(MO(), Bool, m => Maybe.is_some(&2, St.Org, m), None{}, Some{x}, ex))
    case Some{y}:
      match s:
        case St.Store{c, rs, m, gs, rt}:
          L.clash(St.Orgs.holds(i, k, St.Org{i, n, h} <> St.Orgs.drop(i, gs)), Empty,
            PA.known_dealer(k, admin, St.Org{i, n, h} <> St.Orgs.drop(i, gs), i, e),
            old_key_false(i, n, h, k, gs, ne))

law revoked_no_one:
  for +s: St.Store
  for +i: String
  for +h: String
  for +admin: Maybe<&2, String>
  for e: {A.Api.known(h, admin, St.Store.orgs(St.Store.apply(s, St.Revoked{i}))) == A.Dealer{i} : A.Who}
  Empty

def revoked_no_one(s, i, h, admin, e):
  match s:
    case St.Store{c, rs, m, gs, rt}:
      L.clash(St.Orgs.holds(i, h, St.Orgs.drop(i, gs)), Empty, PA.known_dealer(h, admin, St.Orgs.drop(i, gs), i, e), drop_holds(i, h, gs))

law rekey_keeps_others:
  for +found: MO()
  for +s: St.Store
  for +i: String
  for +n: String
  for +k: String
  for +j: String
  for +h: String
  for +ne: {J.Text.same(j, i) == False{} : Bool}
  {St.Orgs.holds(j, h, St.Store.orgs(St.Store.rekey(found, St.Org{i, n, k}, s))) == St.Orgs.holds(j, h, St.Store.orgs(s)) : Bool}

def rekey_keeps_others(found, s, i, n, k, j, h, ne):
  match found:
    case None{}:
      {==}
    case Some{y}:
      match s:
        case St.Store{c, rs, m, gs, rt}:
          %Equal.sym(Bool, J.Text.same(j, i), False{}, ne) : {Bool.or(Bool.and(_, J.Text.same(h, k)), St.Orgs.holds(j, h, St.Orgs.drop(i, gs))) == St.Orgs.holds(j, h, gs) : Bool}
          drop_keeps(j, i, h, gs, ne)

law revoke_keeps_others:
  for +s: St.Store
  for +i: String
  for +j: String
  for +h: String
  for +ne: {J.Text.same(j, i) == False{} : Bool}
  {St.Orgs.holds(j, h, St.Store.orgs(St.Store.apply(s, St.Revoked{i}))) == St.Orgs.holds(j, h, St.Store.orgs(s)) : Bool}

def revoke_keeps_others(s, i, j, h, ne):
  match s:
    case St.Store{c, rs, m, gs, rt}:
      drop_keeps(j, i, h, gs, ne)

law rekey_keeps_recs:
  for +found: MO()
  for +g: St.Org
  for +s: St.Store
  {St.Store.recs(St.Store.rekey(found, g, s)) == St.Store.recs(s) : List<&2, St.Rec>}

def rekey_keeps_recs(found, g, s):
  match found:
    case None{}:
      {==}
    case Some{y}:
      match s:
        case St.Store{c, rs, m, gs, rt}:
          {==}

law rekey_keeps_made:
  for +found: MO()
  for +g: St.Org
  for +s: St.Store
  {St.Store.made(St.Store.rekey(found, g, s)) == St.Store.made(s) : Nat}

def rekey_keeps_made(found, g, s):
  match found:
    case None{}:
      {==}
    case Some{y}:
      match s:
        case St.Store{c, rs, m, gs, rt}:
          {==}

law revoke_keeps_recs:
  for +s: St.Store
  for +i: String
  {St.Store.recs(St.Store.apply(s, St.Revoked{i})) == St.Store.recs(s) : List<&2, St.Rec>}

def revoke_keeps_recs(s, i):
  match s:
    case St.Store{c, rs, m, gs, rt}:
      {==}

law revoke_keeps_made:
  for +s: St.Store
  for +i: String
  {St.Store.made(St.Store.apply(s, St.Revoked{i})) == St.Store.made(s) : Nat}

def revoke_keeps_made(s, i):
  match s:
    case St.Store{c, rs, m, gs, rt}:
      {==}

law revoked_on_record:
  for +s: St.Store
  for +i: String
  for +g: St.Org
  for +e: {St.Orgs.find(i, St.Store.orgs(s)) == Some{g} : MO()}
  {St.Store.org(i, St.Store.apply(s, St.Revoked{i})) == Some{g} : MO()}

def revoked_on_record(s, i, g, e):
  match s:
    case St.Store{c, rs, m, gs, rt}:
      %Equal.sym(MO(), St.Orgs.find(i, St.Orgs.drop(i, gs)), None{}, drop_find(i, gs)) : {St.Store.org.pick(_, St.Orgs.find(i, St.Orgs.retire(St.Orgs.find(i, gs), rt))) == Some{g} : MO()}
      %Equal.sym(MO(), St.Orgs.find(i, gs), Some{g}, e) : {St.Orgs.find(i, St.Orgs.retire(_, rt)) == Some{g} : MO()}
      %Equal.sym(Bool, J.Text.same(i, St.Org.id(g)), True{}, find_same(i, gs, g, e)) : {St.Orgs.pick(_, g, St.Orgs.find(i, rt)) == Some{g} : MO()}
      {==}
