package national.data.computation;

import java.util.ArrayList;
import java.util.List;
import national.ElectionConstants;

/**
 * @author Ólavur Kjølbro
 */
public class StepFourDraw {

	private int ranking;
	private List<ProvinceResult> province_results;
	private List<PartyResult> party_results;

	//@ invariant province_results != null;
	//@ invariant party_results != null;
	//@ invariant ranking > 0 && ranking <= ElectionConstants.ADDITIONAL_SEATS;

	//@ pre rank > 0 && rank <= ElectionConstants.ADDITIONAL_SEATS;
	//@ post ranking == rank;
	public StepFourDraw(int rank) {
		this.ranking = rank;
		province_results = new ArrayList<ProvinceResult>();
		party_results = new ArrayList<PartyResult>();
	}

	/**
	 * @return the ranking
	 */
	public /*@ pure @*/ int getRanking() {
		return ranking;
	}

	/**
	 * @return the province_results
	 */
	public /*@ pure @*/ List<ProvinceResult> getProvinceResults() {
		return province_results;
	}

	/**
	 * @return the party_results
	 */
	public /*@ pure @*/ List<PartyResult> getPartyResults() {
		return party_results;
	}
}