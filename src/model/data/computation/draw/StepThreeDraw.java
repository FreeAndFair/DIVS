package model.data.computation.draw;

import java.util.ArrayList;
import java.util.List;

import model.data.computation.PartyResult;

/**
 * @author Ólavur Kjølbro
 */
public class StepThreeDraw {

	private List<PartyResult> parties;
	
	//@ invariant parties != null;

	public StepThreeDraw() {
		this.parties = new ArrayList<PartyResult>();
	}

	/**
	 * @return the parties
	 */
	public /*@ pure @*/ List<PartyResult> getParties() {
		return parties;
	}
}