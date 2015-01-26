package model.data.computation.draw;

import java.util.ArrayList;
import java.util.List;

import model.data.computation.CandidateResult;
import model.data.computation.ConstituencyResult;
import model.data.computation.PartyResult;

/**
 * @author Ólavur Kjølbro
 */
public class StepSixDraw {

	private ConstituencyResult cr;
	private PartyResult presc;
	private List<CandidateResult> candidates;

	//@ invariant presc != null;
	//@ invariant cr != null;

	public StepSixDraw(
			/*@ non_null @*/ ConstituencyResult cr,
			/*@ non_null @*/ PartyResult pres) {
		this.cr = cr;
		this.presc = pres;
		this.candidates = new ArrayList<CandidateResult>();
	}

	/**
	 * @return the cr
	 */
	public ConstituencyResult getConstituencyResult() {
		return cr;
	}

	/**
	 * @return the party result
	 */
	public /*@ pure @*/ PartyResult getPartyResult() {
		return presc;
	}

	/**
	 * @return the candidates
	 */
	public /*@ pure @*/ List<CandidateResult> getCandidates() {
		return candidates;
	}

}
