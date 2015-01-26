package model.data.computation.draw;

import java.util.ArrayList;
import java.util.List;

import model.data.computation.CandidateResult;
import model.data.computation.ConstituencyResult;
import model.data.computation.PartyResult;

/**
 * @author Ólavur Kjølbro
 */
public class StepOneDraw {

	private ConstituencyResult cr;
	private List<PartyResult> parties;
	private List<CandidateResult> candidates;

	//@ invariant cr != null;
	//@ invariant parties != null;

	public StepOneDraw(/*@ non_null @*/ ConstituencyResult cr) {
		this.cr = cr;
		this.parties = new ArrayList<PartyResult>();
		this.candidates = new ArrayList<CandidateResult>();
	}

	/**
	 * @return the cr
	 */
	public /*@ pure @*/ ConstituencyResult getConstituencyResult() {
		return cr;
	}

	/**
	 * @return the parties
	 */
	public /*@ pure @*/ List<PartyResult> getParties() {
		return parties;
	}

	/**
	 * @return the candidates
	 */
	public /*@ pure @*/ List<CandidateResult> getCandidates() {
		return candidates;
	}
}
