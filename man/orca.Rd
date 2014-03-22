\name{orca}
\alias{count4}
\alias{count5}
\alias{ecount4}
\alias{ecount5}
\title{Orbit counting} 

\description{
Count the node or edge orbits in 4- or 5- node graphlets for all nodes (edges) in the given graph.
}

\usage{
count4(graph)
count5(graph)
ecount4(graph)
ecount5(graph)
}
\arguments{
  \item{graph}{A graph given as a nx2 edge matrix, a data frame with edges or a graph object from the package 'graph'. The nodes in the matrix or data frame are given by integer indices that start with 1.
}
}
%% \details{}
\value{
A numeric matrix or orbit counts. Rows correspond to graph nodes or edges in the same order as on the input, and the columns corresponding to orbits.
}
\references{
Tomaz Hocevar, Janez Demsar (2014): A combinatorial approach to graphlet counting. Bioinformatics.
}
\author{
Tomaz Hocevar and Janez Demsar}

%% ~Make other sections like Warning with \section{Warning }{....} ~

\examples{
library(orca)
data("karate")

count4(karate)
}
% Add one or more standard keywords, see file 'KEYWORDS' in the
% R documentation directory.
\keyword{graphs}
