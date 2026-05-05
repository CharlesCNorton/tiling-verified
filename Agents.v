From Stdlib Require Import Lists.List.
Import ListNotations.
From Tiling Require Export Calculus.

Record AgentRecord : Type := mkAgent {
  agent_level : nat;
  agent_goal : Form;
  agent_action_space : list Form;
  agent_decision : Form -> Form;
  agent_verification : Form -> bool
}.

Definition agent_licenses (A : AgentRecord) (sigma : Form) : Form :=
  if agent_verification A sigma
  then agent_decision A sigma
  else Bot.

Definition Box_licenses_via_agent (A : AgentRecord) (sigma : Form) : Form :=
  Box (agent_level A) (agent_licenses A sigma).

Definition canonical_box_n_agent (n : nat) (G : Form) : AgentRecord :=
  mkAgent n G [] (fun phi => phi) (fun _ => true).

