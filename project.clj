(defproject equilibrium "0.1.0-SNAPSHOT"
  :description "FIXME: write description"
  :url "http://example.com/FIXME"
  :license {:name "Eclipse Public License"
            :url "http://www.eclipse.org/legal/epl-v10.html"}
  :dependencies [[org.clojure/clojure "1.9.0"]
                 [org.clojure/core.unify "0.5.7"]]
  :profiles {:dev {:dependencies [[midje "1.9.1" :exclusions [org.clojure/clojure]]]
                   :plugins [[lein-midje "3.2.1"]]}})
